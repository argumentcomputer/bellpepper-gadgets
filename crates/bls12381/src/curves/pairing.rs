use std::marker::PhantomData;

use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, SynthesisError,
};
use bls12_381::fp12::Fp12 as BlsFp12;
use bls12_381::fp2::Fp2 as BlsFp2;
use bls12_381::fp6::Fp6 as BlsFp6;
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigInt;

use crate::fields::{fp12::Fp12Element, fp2::Fp2Element, fp6::Fp6Element, torus::Torus};

use super::{g1::G1Point, g2::G2Point};

pub trait EmulatedPairing<F, G1Element, G2Element, GtElement>
where
    F: PrimeField + PrimeFieldBits,
{
    fn miller_loop<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: impl AsRef<[G1Element]>,
        g2: impl AsRef<[G2Element]>,
    ) -> Result<GtElement, SynthesisError>;

    fn final_exponentiation<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        gt: &GtElement,
        is_single_pairing: bool,
    ) -> Result<GtElement, SynthesisError>;

    fn pair<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: impl AsRef<[G1Element]>,
        g2: impl AsRef<[G2Element]>,
    ) -> Result<GtElement, SynthesisError>;

    fn assert_pairing_check<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: impl AsRef<[G1Element]>,
        g2: impl AsRef<[G2Element]>,
    ) -> Result<(), SynthesisError>;
}

pub struct EmulatedBls12381Pairing<F> {
    _f: PhantomData<F>,
}

/// LineEval represents a sparse Fp12 Elmt (result of the line evaluation)
/// line: 1 + R0(x/y) + R1(1/y) = 0 instead of R0'*y + R1'*x + R2' = 0 This
/// makes the multiplication by lines (MulBy014)
pub struct LineEval<F: PrimeField + PrimeFieldBits> {
    pub(crate) r0: Fp2Element<F>,
    pub(crate) r1: Fp2Element<F>,
}
impl<F: PrimeField + PrimeFieldBits> LineEval<F> {
    fn zero() -> Self {
        Self {
            r0: Fp2Element::zero(),
            r1: Fp2Element::zero(),
        }
    }
}

pub struct LineEvals<F: PrimeField + PrimeFieldBits> {
    pub(crate) v0: Vec<LineEval<F>>,
    pub(crate) v1: Vec<LineEval<F>>,
}
impl<F: PrimeField + PrimeFieldBits> LineEvals<F> {
    fn new() -> Self {
        let mut res = Self {
            v0: Vec::with_capacity(LOOP_COUNTER.len() - 1),
            v1: Vec::with_capacity(LOOP_COUNTER.len() - 1),
        };
        for _ in 0..(LOOP_COUNTER.len() - 1) {
            res.v0.push(LineEval::zero());
            res.v1.push(LineEval::zero());
        }
        res
    }
}

/// LOOP_COUNTER = seed in binary
///
/// seed=-15132376222941642752
const LOOP_COUNTER: [u8; 64] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1,
];

impl<F: PrimeField + PrimeFieldBits> EmulatedBls12381Pairing<F> {
    pub fn compute_lines<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        q: &G2Point<F>,
    ) -> Result<LineEvals<F>, SynthesisError> {
        let cs = &mut cs.namespace(|| "Pairing::compute_lines(q)");
        let mut res = LineEvals::<F>::new();
        let n = LOOP_COUNTER.len();
        let mut q_acc = q.clone();

        let (tmpq, tmp0, tmp1) = Self::triple_step(cs, &q_acc)?;
        q_acc = tmpq;
        res.v0[n - 2] = tmp0;
        res.v1[n - 2] = tmp1;
        let mut i = n - 3;
        let mut j = 1;
        while i >= 1 {
            if LOOP_COUNTER[i] == 0 {
                let (tmpq, tmp0) = Self::double_step(
                    &mut cs.namespace(|| format!("q_acc,tmp0 <- double_step(q_acc) ({i})")),
                    &q_acc,
                )?;
                q_acc = tmpq;
                res.v0[i] = tmp0;
            } else {
                let (tmpq, tmp0, tmp1) = Self::double_and_add_step(
                    &mut cs.namespace(|| {
                        format!("q_acc,tmp0,tmp1 <- double_and_add_step(q_acc) ({i})")
                    }),
                    &q_acc,
                    q,
                )?;
                q_acc = tmpq;
                res.v0[i] = tmp0;
                res.v1[i] = tmp1;
            }

            // TODO: This fails with an overflow without an explicit reduce call every few iterations, even though theoretically this should be happening automatically.
            if j % 16 == 0 {
                q_acc =
                    q_acc.reduce(&mut cs.namespace(|| format!("q_acc <- q_acc.reduce() ({i})")))?;
            }

            i -= 1;
            j += 1;
        }
        let tmp0 = Self::tangent_compute(cs, &q_acc)?;
        res.v0[0] = tmp0;

        Ok(res)
    }

    #[allow(clippy::type_complexity)]
    /// triple_step triples p1 in affine coordinates, and evaluates the line in Miller loop
    pub fn triple_step<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        p: &G2Point<F>,
    ) -> Result<(G2Point<F>, LineEval<F>, LineEval<F>), SynthesisError> {
        let cs = &mut cs.namespace(|| "triple_step(p)");
        // λ1 = 3x²/2y
        let n = p.x.square(&mut cs.namespace(|| "n <- p.x.square()"))?;
        let n = n.mul_const(&mut cs.namespace(|| "n <- n * 3"), &BigInt::from(3))?;
        let d = p.y.double(&mut cs.namespace(|| "d <- p.y.double()"))?;
        let l1 = n.div_unchecked(&mut cs.namespace(|| "l1 <- n div d"), &d)?;

        // compute line1
        let l1r0 = l1.clone();
        let l1r1 = l1.mul(&mut cs.namespace(|| "l1r1 <- l1 * p.x"), &p.x)?;
        let l1r1 = l1r1.sub(&mut cs.namespace(|| "l1r1 <- l1r1 - p.y"), &p.y)?;
        let line1 = LineEval { r0: l1r0, r1: l1r1 };

        // x2 = λ1²-2x
        let x2 = l1.square(&mut cs.namespace(|| "x2 <- l1.square()"))?;
        let x2 = x2.sub(&mut cs.namespace(|| "x2 <- x2 - p.x"), &p.x)?;
        let x2 = x2.sub(&mut cs.namespace(|| "x2 <- x2 - p.x (2)"), &p.x)?;

        // ommit yr computation, and
        // compute λ2 = 2y/(x2 − x) − λ1.
        let x1x2 = p.x.sub(&mut cs.namespace(|| "x1x2 <- p.x - x2"), &x2)?;
        let l2 = d.div_unchecked(&mut cs.namespace(|| "l2 <- d div x1x2"), &x1x2)?;
        let l2 = l2.sub(&mut cs.namespace(|| "l2 <- l2 - l1"), &l1)?;

        // compute line2
        let l2r0 = l2.clone();
        let l2r1 = l2.mul(&mut cs.namespace(|| "l2r1 <- l2 * p.x"), &p.x)?;
        let l2r1 = l2r1.sub(&mut cs.namespace(|| "l2r1 <- l2r1 - p.y"), &p.y)?;
        let line2 = LineEval { r0: l2r0, r1: l2r1 };

        // xr = λ²-p.x-x2
        let l2l2 = l2.square(&mut cs.namespace(|| "l2l2 <- l2.square()"))?;
        let qxrx = x2.add(&mut cs.namespace(|| "qxrx = x2 + p.x"), &p.x)?;
        let xr = l2l2.sub(&mut cs.namespace(|| "xr <- l2l2 - qxrx"), &qxrx)?;

        // yr = λ(p.x-xr) - p.y
        let pxrx = p.x.sub(&mut cs.namespace(|| "pxrx <- p.x - xr"), &xr)?;
        let l2pxrx = l2.mul(&mut cs.namespace(|| "l2pxrx <- l2 * pxrx"), &pxrx)?;
        let yr = l2pxrx.sub(&mut cs.namespace(|| "yr <- l2pxrx - p.y"), &p.y)?;

        Ok((G2Point { x: xr, y: yr }, line1, line2))
    }

    /// double_step doubles a point in affine coordinates, and evaluates the line in Miller loop
    pub fn double_step<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        p: &G2Point<F>,
    ) -> Result<(G2Point<F>, LineEval<F>), SynthesisError> {
        let cs = &mut cs.namespace(|| "double_step(p)");
        // λ = 3x²/2y
        let n = p.x.square(&mut cs.namespace(|| "n <- p.x.square()"))?;
        let n = n.mul_const(&mut cs.namespace(|| "n <- n * 3"), &BigInt::from(3))?;
        let d = p.y.double(&mut cs.namespace(|| "d <- p.y.double()"))?;
        let l = n.div_unchecked(&mut cs.namespace(|| "l <- n div d"), &d)?;

        // xr = λ²-2x
        let xr = l.square(&mut cs.namespace(|| "xr <- l.square()"))?;
        let xr = xr.sub(&mut cs.namespace(|| "xr <- xr - p.x"), &p.x)?;
        let xr = xr.sub(&mut cs.namespace(|| "xr <- xr - p.x (2)"), &p.x)?;

        // yr = λ(x-xr)-y
        let yr = p.x.sub(&mut cs.namespace(|| "yr <- p.x - xr"), &xr)?;
        let yr = l.mul(&mut cs.namespace(|| "yr <- l * yr"), &yr)?;
        let yr = yr.sub(&mut cs.namespace(|| "yr <- yr - p.y"), &p.y)?;

        let r0 = l.clone();
        let r1 = l.mul(&mut cs.namespace(|| "r1 <- l * p.x"), &p.x)?;
        let r1 = r1.sub(&mut cs.namespace(|| "r1 <- r1 - p.y"), &p.y)?;

        Ok((G2Point { x: xr, y: yr }, LineEval { r0, r1 }))
    }

    #[allow(clippy::type_complexity)]
    /// double_and_add_step doubles p1 and adds p2 to the result in affine coordinates, and evaluates the line in Miller loop
    /// https://eprint.iacr.org/2022/1162 (Section 6.1)/
    pub fn double_and_add_step<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        p1: &G2Point<F>,
        p2: &G2Point<F>,
    ) -> Result<(G2Point<F>, LineEval<F>, LineEval<F>), SynthesisError> {
        let cs = &mut cs.namespace(|| "double_and_add_step(p1, p2)");
        // compute λ1 = (y2-y1)/(x2-x1)
        let n = p1.y.sub(&mut cs.namespace(|| "n <- p1.y - p2.y"), &p2.y)?;
        let d = p1.x.sub(&mut cs.namespace(|| "d <- p1.x - p2.x"), &p2.x)?;
        let l1 = n.div_unchecked(&mut cs.namespace(|| "l1 <- n div d"), &d)?;

        // compute x3 =λ1²-x1-x2
        let x3 = l1.square(&mut cs.namespace(|| "x3 <- l1.square()"))?;
        let x3 = x3.sub(&mut cs.namespace(|| "x3 <- x3 - p1.x"), &p1.x)?;
        let x3 = x3.sub(&mut cs.namespace(|| "x3 <- x3 - p2.x"), &p2.x)?;

        // omit y3 computation

        // compute line1
        let l1r0 = l1.clone();
        let l1r1 = l1.mul(&mut cs.namespace(|| "l1r1 <- l1 * p1.x"), &p1.x)?;
        let l1r1 = l1r1.sub(&mut cs.namespace(|| "l1r1 <- l1r1 - p.1y"), &p1.y)?;
        let line1 = LineEval { r0: l1r0, r1: l1r1 };

        // compute λ2 = -λ1-2y1/(x3-x1)
        let n = p1.y.double(&mut cs.namespace(|| "n <- p1.y.double()"))?;
        let d = x3.sub(&mut cs.namespace(|| "d <- x3 - p1.x"), &p1.x)?;
        let l2 = n.div_unchecked(&mut cs.namespace(|| "l2 <- n div d"), &d)?;
        let l2 = l2.add(&mut cs.namespace(|| "l2 <- l2 + l1"), &l1)?;
        let l2 = l2.neg(&mut cs.namespace(|| "l2 <- l2.neg()"))?;

        // compute x4 = λ2²-x1-x3
        let x4 = l2.square(&mut cs.namespace(|| "x4 <- l2.square()"))?;
        let x4 = x4.sub(&mut cs.namespace(|| "x4 <- x4 - p1.x"), &p1.x)?;
        let x4 = x4.sub(&mut cs.namespace(|| "x4 <- x4 - x3"), &x3)?;

        // compute y4 = λ2(x1 - x4)-y1
        let y4 = p1.x.sub(&mut cs.namespace(|| "y4 <- p1.x - x4"), &x4)?;
        let y4 = l2.mul(&mut cs.namespace(|| "y4 <- l2 * y4"), &y4)?;
        let y4 = y4.sub(&mut cs.namespace(|| "y4 <- y4 - p1.y"), &p1.y)?;

        // compute line2
        let l2r0 = l2.clone();
        let l2r1 = l2.mul(&mut cs.namespace(|| "l2r1 <- l2 * p1.x"), &p1.x)?;
        let l2r1 = l2r1.sub(&mut cs.namespace(|| "l2r1 <- l2r1 - p1.y"), &p1.y)?;
        let line2 = LineEval { r0: l2r0, r1: l2r1 };

        Ok((G2Point { x: x4, y: y4 }, line1, line2))
    }

    /// tangent_compute computes the line that goes through p1 and p2 but does not compute p1+p2
    pub fn tangent_compute<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        p: &G2Point<F>,
    ) -> Result<LineEval<F>, SynthesisError> {
        let cs = &mut cs.namespace(|| "tangent_compute(p)");
        // λ = 3x²/2y
        let n = p.x.square(&mut cs.namespace(|| "n <- p.x.square()"))?;
        let n = n.mul_const(&mut cs.namespace(|| "n <- n * 3"), &BigInt::from(3))?;
        let d = p.y.double(&mut cs.namespace(|| "d <- p.y.double()"))?;
        let l = n.div_unchecked(&mut cs.namespace(|| "l <- n div d"), &d)?;

        let r0 = l.clone();
        let r1 = l.mul(&mut cs.namespace(|| "r1 <- l * p.x"), &p.x)?;
        let r1 = r1.sub(&mut cs.namespace(|| "r1 <- r1 - p.y"), &p.y)?;

        Ok(LineEval { r0, r1 })
    }

    /// miller_loop_lines computes the multi-Miller loop from points in G1 and precomputed lines in G2
    fn miller_loop_lines<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: impl AsRef<[G1Point<F>]>,
        g2_lines: impl AsRef<[LineEvals<F>]>,
    ) -> Result<Fp12Element<F>, SynthesisError> {
        let cs = &mut cs.namespace(|| "miller_loop_lines(p, l)");
        let (p, lines) = (g1.as_ref(), g2_lines.as_ref());
        assert!(
            !p.is_empty() && p.len() == lines.len(),
            "mismatching miller_loop_lines lengths"
        ); // just assert since we check in miller_loop properly
        let n = p.len();

        // precomputation
        let mut y_inv = Vec::with_capacity(n);
        let mut x_neg_over_y = Vec::with_capacity(n);
        for (k, pt) in p.iter().enumerate() {
            // P are supposed to be on G1 respectively of prime order r.
            // The point (x,0) is of order 2. But this function does not check
            // subgroup membership.
            let y =
                pt.y.inverse(&mut cs.namespace(|| format!("y_inv[{k}] <- p[{k}].y.inverse()")))?;
            let x = pt.x.mul(
                &mut cs.namespace(|| format!("x_neg_over_y[{k}] <- p[{k}].x * y_inv[{k}]")),
                &y,
            )?;
            let x = x.neg(
                &mut cs.namespace(|| format!("x_neg_over_y[{k}] <- x_neg_over_y[{k}].neg()")),
            )?;

            y_inv.push(y);
            x_neg_over_y.push(x);
        }

        // TODO: there should be some unnecessary allocs due to how we're overwriting some res values below, double check
        let mut res =
            Fp12Element::alloc_element(&mut cs.namespace(|| "res <- 1"), &BlsFp12::one())?;

        // Compute ∏ᵢ { fᵢ_{x₀,Q}(P) }

        // i = 62, separately to avoid an Fp12 Square
        // (Square(res) = 1² = 1)
        // k = 0, separately to avoid MulBy014 (res × ℓ)
        res.c0.b0 = lines[0].v0[62]
            .r1
            .mul_element(
                &mut cs.namespace(|| "res.c0.b0 <- l[0][0][62].r1 * y_inv[0]"),
                &y_inv[0],
            )?
            .clone();
        res.c0.b1 = lines[0].v0[62]
            .r0
            .mul_element(
                &mut cs.namespace(|| "res.c0.b1 <- l[0][0][62].r0 * x_neg_over_y[0]"),
                &x_neg_over_y[0],
            )?
            .clone();
        res.c1.b1 =
            Fp2Element::alloc_element(&mut cs.namespace(|| "res.c1.b1 <- 1"), &BlsFp2::one())?;

        let tmp0 = lines[0].v1[62].r1.mul_element(
            &mut cs.namespace(|| "tmp0 <- l[0][1][62].r1 * y_inv[0]"),
            &y_inv[0],
        )?;
        let tmp1 = lines[0].v1[62].r0.mul_element(
            &mut cs.namespace(|| "tmp1 <- l[0][1][62].r0 * x_neg_over_y[0]"),
            &x_neg_over_y[0],
        )?;
        let mut res = Fp12Element::mul_014_by_014(
            &mut cs.namespace(|| "res <- mul_014_by_014(tmp0, tmp1, res.c0.b0, res.c0.b1"),
            &tmp0,
            &tmp1,
            &res.c0.b0,
            &res.c0.b1,
        )?;

        for k in 1..n {
            let tmp0 = lines[k].v0[62].r1.mul_element(
                &mut cs.namespace(|| format!("tmp0 <- l[{k}][0][62].r1 * y_inv[{k}]")),
                &y_inv[k],
            )?;
            let tmp1 = lines[k].v0[62].r0.mul_element(
                &mut cs.namespace(|| format!("tmp1 <- l[{k}][0][62].r0 * x_neg_over_y[{k}]")),
                &x_neg_over_y[k],
            )?;
            res = res.mul_by_014(
                &mut cs.namespace(|| format!("res <- res * 014(tmp0, tmp1) ({k})")),
                &tmp0,
                &tmp1,
            )?;

            let tmp0 = lines[k].v1[62].r1.mul_element(
                &mut cs.namespace(|| format!("tmp0 <- l[{k}][1][62].r1 * y_inv[{k}]")),
                &y_inv[k],
            )?;
            let tmp1 = lines[k].v1[62].r0.mul_element(
                &mut cs.namespace(|| format!("tmp1 <- l[{k}][1][62].r0 * x_neg_over_y[{k}]")),
                &x_neg_over_y[k],
            )?;
            res = res.mul_by_014(
                &mut cs.namespace(|| format!("res <- res * 014(tmp0, tmp1) (2) ({k})")),
                &tmp0,
                &tmp1,
            )?;
        }

        for i in (0..=61).rev() {
            // mutualize the square among n Miller loops
            // (∏ᵢfᵢ)²
            res = res.square(&mut cs.namespace(|| format!("res <- res.square() ({i})")))?;

            for k in 0..n {
                let tmp0 = lines[k].v0[i].r1.mul_element(
                    &mut cs.namespace(|| format!("tmp0 <- l[{k}][0][{i}].r1 * y_inv[{k}]")),
                    &y_inv[k],
                )?;
                let tmp1 = lines[k].v0[i].r0.mul_element(
                    &mut cs.namespace(|| format!("tmp1 <- l[{k}][0][{i}].r0 * x_neg_over_y[{k}]")),
                    &x_neg_over_y[k],
                )?;
                res = res.mul_by_014(
                    &mut cs.namespace(|| format!("res <- res * 014(tmp0, tmp1) ({k}-{i})")),
                    &tmp0,
                    &tmp1,
                )?;
                if LOOP_COUNTER[i] == 1 {
                    let tmp0 = lines[k].v1[i].r1.mul_element(
                        &mut cs.namespace(|| format!("tmp0 <- l[{k}][1][{i}].r1 * y_inv[{k}]")),
                        &y_inv[k],
                    )?;
                    let tmp1 = lines[k].v1[i].r0.mul_element(
                        &mut cs
                            .namespace(|| format!("tmp1 <- l[{k}][1][{i}].r0 * x_neg_over_y[{k}]")),
                        &x_neg_over_y[k],
                    )?;
                    res = res.mul_by_014(
                        &mut cs.namespace(|| format!("res <- res * 014(tmp0, tmp1) (2) ({k}-{i})")),
                        &tmp0,
                        &tmp1,
                    )?;
                }
            }
        }

        // negative x₀
        res = res.conjugate(&mut cs.namespace(|| "res <- res.conjugate()"))?;

        Ok(res)
    }
}

impl<F> EmulatedPairing<F, G1Point<F>, G2Point<F>, Fp12Element<F>> for EmulatedBls12381Pairing<F>
where
    F: PrimeField + PrimeFieldBits,
{
    /// miller_loop computes the multi-Miller loop
    /// ∏ᵢ { fᵢ_{u,Q}(P) }
    fn miller_loop<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: impl AsRef<[G1Point<F>]>,
        g2: impl AsRef<[G2Point<F>]>,
    ) -> Result<Fp12Element<F>, SynthesisError> {
        let (p, q) = (g1.as_ref(), g2.as_ref());
        if p.is_empty() || p.len() != q.len() {
            return Err(SynthesisError::IncompatibleLengthVector(format!(
                "miller loop: {} vs {}",
                p.len(),
                q.len()
            )));
        }

        // TODO: implement precompute_lines and omit line computation for constant elements here
        let lines: Vec<LineEvals<F>> = q
            .iter()
            .enumerate()
            .map(|(idx, pq)| {
                Self::compute_lines(&mut cs.namespace(|| format!("compute_lines(q[{idx}])")), pq)
            })
            .collect::<Result<_, _>>()?;

        Self::miller_loop_lines(cs, p, lines)
    }

    fn final_exponentiation<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        gt: &Fp12Element<F>,
        is_single_pairing: bool,
    ) -> Result<Fp12Element<F>, SynthesisError> {
        let cs = &mut cs.namespace(|| format!("final_exponentiation(e, {is_single_pairing})"));
        let mut e = gt.clone();
        let mut sel1: Option<AllocatedBit> = None;
        let mut dummy: Option<Fp6Element<F>> = None;

        // 1. Easy part
        // (p⁶-1)(p²+1)

        if is_single_pairing {
            // The Miller loop result is ≠ {-1,1}, otherwise this means P and Q are
            // linearly dependant and not from G1 and G2 respectively.
            // So e ∈ G_{q,2} \ {-1,1} and hence e.C1 ≠ 0.
            // Nothing to do.
        } else {
            // However, for a product of Miller loops (n>=2) this might happen.  If this is
            // the case, the result is 1 in the torus. We assign a dummy value (1) to e.C1
            // and proceed further.
            dummy = Some(Fp6Element::<F>::alloc_element(
                &mut cs.namespace(|| "alloc dummy"),
                &BlsFp6::one(),
            )?); // TODO: do we need to explicit alloc here or could this be a constant?
            sel1 = Some(e.c1.alloc_is_zero(&mut cs.namespace(|| "sel1 <- e.c1.is_zero()"))?);
            e = Fp12Element {
                c0: e.c0,
                c1: Fp6Element::conditionally_select(
                    &mut cs.namespace(|| "e.c1 <- select(dummy, e.c1, sel1)"),
                    dummy.as_ref().unwrap(),
                    &e.c1,
                    &Boolean::Is(sel1.clone().unwrap()),
                )?,
            };
        }

        // Torus compression absorbed:
        // Raising e to (p⁶-1) is
        // e^(p⁶) / e = (e.C0 - w*e.C1) / (e.C0 + w*e.C1)
        //            = (-e.C0/e.C1 + w) / (-e.C0/e.C1 - w)
        // So the fraction -e.C0/e.C1 is already in the torus.
        // This absorbs the torus compression in the easy part.
        let c =
            e.c0.div_unchecked(&mut cs.namespace(|| "c <- e.c0 div e.c1"), &e.c1)?;
        let c = c.neg(&mut cs.namespace(|| "c <- c.neg()"))?;
        let ct = Torus(c);
        let t0 = ct.frobenius_square(&mut cs.namespace(|| "t0 <- ct.frobenius_square()"))?;
        let ct = t0.mul(&mut cs.namespace(|| "ct <- t0 * ct"), &ct)?;

        // 2. Hard part (up to permutation)
        // 3(p⁴-p²+1)/r
        // Daiki Hayashida, Kenichiro Hayasaka and Tadanori Teruya
        // https://eprint.iacr.org/2020/875.pdf
        // performed in torus compressed form
        let t0 = ct.square(&mut cs.namespace(|| "t0 <- ct.square()"))?;
        let t1 = t0.expt_half(&mut cs.namespace(|| "t1 <- t0.expt_half()"))?;
        let t2 = ct.inverse(&mut cs.namespace(|| "t2 <- ct.inverse()"))?;
        let t1 = t1.mul(&mut cs.namespace(|| "t1 <- t1 * t2"), &t2)?;
        let t2 = t1.expt(&mut cs.namespace(|| "t2 <- t1.expt()"))?;
        let t1 = t1.inverse(&mut cs.namespace(|| "t1 <- t1.inverse()"))?;
        let t1 = t1.mul(&mut cs.namespace(|| "t1 <- t1 * t2 (2)"), &t2)?;
        let t2 = t1.expt(&mut cs.namespace(|| "t2 <- t1.expt() (2)"))?;
        let t1 = t1.frobenius(&mut cs.namespace(|| "t1 <- t1.frobenius()"))?;
        let t1 = t1.mul(&mut cs.namespace(|| "t1 <- t1 * t2 (3)"), &t2)?;
        let ct = ct.mul(&mut cs.namespace(|| "ct <- ct * t0"), &t0)?;
        let t0 = t1.expt(&mut cs.namespace(|| "t0 <- t1.expt()"))?;
        let t2 = t0.expt(&mut cs.namespace(|| "t2 <- t0.expt()"))?;
        let t0 = t1.frobenius_square(&mut cs.namespace(|| "t0 <- t1.frobenius_square()"))?;
        let t1 = t1.inverse(&mut cs.namespace(|| "t1 <- t1.inverse() (2)"))?;
        let t1 = t1.mul(&mut cs.namespace(|| "t1 <- t1 * t2 (4)"), &t2)?;
        let t1 = t1.mul(&mut cs.namespace(|| "t1 <- t1 * t0"), &t0)?;

        // MulTorus(c, t1) requires c ≠ -t1. When c = -t1, it means the
        // product is 1 in the torus.
        if is_single_pairing {
            // For a single pairing, this does not happen because the pairing is non-degenerate.
            let res = ct.mul(&mut cs.namespace(|| "res <- ct * t1"), &t1)?;
            let res = res.decompress(&mut cs.namespace(|| "res <- res.decompress()"))?;
            Ok(res)
        } else {
            // For a product of pairings this might happen when the result is expected to be 1.
            // We assign a dummy value (1) to t1 and proceed furhter.
            // Finally we do a select on both edge cases:
            //   - Only if seletor1=0 and selector2=0, we return MulTorus(c, t1) decompressed.
            //   - Otherwise, we return 1.
            let c = ct.0; // rip out the Fp6s out of the torus elements
            let t1 = t1.0;
            let sum = c.add(&mut cs.namespace(|| "sum <- c + t1 (e6)"), &t1)?;
            let sel2: AllocatedBit =
                sum.alloc_is_zero(&mut cs.namespace(|| "sel2 <- sum.is_zero()"))?;
            let t1 = Fp6Element::conditionally_select(
                &mut cs.namespace(|| "t1 <- select(dummy, t1, sel2)"),
                &dummy.unwrap(),
                &t1,
                &Boolean::Is(sel2.clone()),
            )?;
            let selector = AllocatedBit::nor(
                &mut cs.namespace(|| "selector <- nor(sel1, sel2)"),
                &sel1.unwrap(),
                &sel2,
            )?;
            let ct = Torus(c);
            let t1 = Torus(t1);
            let res = ct.mul(&mut cs.namespace(|| "res <- ct * t1"), &t1)?;
            let res = res.decompress(&mut cs.namespace(|| "res <- res.decompress()"))?;
            let dummy2 = Fp12Element::<F>::alloc_element(
                &mut cs.namespace(|| "alloc dummy2"),
                &BlsFp12::one(),
            )?; // TODO: does this need an explicit alloc or could this be a constant?
            let res = Fp12Element::conditionally_select(
                &mut cs.namespace(|| "res <- select(res, 1, selector)"),
                &res,
                &dummy2,
                &Boolean::Is(selector),
            )?;
            Ok(res)
        }
    }

    fn pair<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: impl AsRef<[G1Point<F>]>,
        g2: impl AsRef<[G2Point<F>]>,
    ) -> Result<Fp12Element<F>, SynthesisError> {
        let p_len = g1.as_ref().len();
        let res = Self::miller_loop(cs, g1, g2)?;
        let res = Self::final_exponentiation(cs, &res, p_len == 1)?;
        Ok(res)
    }

    fn assert_pairing_check<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: impl AsRef<[G1Point<F>]>,
        g2: impl AsRef<[G2Point<F>]>,
    ) -> Result<(), SynthesisError> {
        let res = Self::pair(cs, g1, g2)?;
        let one = Fp12Element::<F>::one();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "pair(p, q) =? 1"), &res, &one)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    // use super::*;
    // use bellpepper_core::test_cs::TestConstraintSystem;
    // use pasta_curves::group::Group;
    // use pasta_curves::Fp;

    // use bls12_381::{G1Affine, G1Projective, G2Affine, G2Projective};

    // use expect_test::{expect, Expect};
    // fn expect_eq(computed: usize, expected: Expect) {
    //     expected.assert_eq(&computed.to_string());
    // }

    // NOTE: this test currently takes ~100GB of ram and a few minutes to run, so it's commented out
    // #[test]
    // fn test_random_pairing() {
    //     let mut rng = rand::thread_rng();
    //     let a = G1Projective::random(&mut rng);
    //     let b = G2Projective::random(&mut rng);
    //     let a = G1Affine::from(a);
    //     let b = G2Affine::from(b);
    //     let c = bls12_381::pairing(&a, &b);
    //     let c = c.0;

    //     let mut cs = TestConstraintSystem::<Fp>::new();
    //     let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
    //     let b_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
    //     let c_alloc = Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
    //     let res_alloc = EmulatedBls12381Pairing::pair(
    //         &mut cs.namespace(|| "pair(a, b)"),
    //         &[a_alloc],
    //         &[b_alloc],
    //     )
    //     .unwrap();
    //     Fp12Element::assert_is_equal(&mut cs.namespace(|| "pair(a, b) = c"), &res_alloc, &c_alloc)
    //         .unwrap();
    //     if !cs.is_satisfied() {
    //         eprintln!("{:?}", cs.which_is_unsatisfied())
    //     }
    //     assert!(cs.is_satisfied());
    //     expect_eq(cs.num_inputs(), expect!["1"]);
    //     expect_eq(cs.scalar_aux().len(), expect!["27479875"]);
    //     expect_eq(cs.num_constraints(), expect!["27589382"]);
    // }
}
