use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_emulated::field_element::EmulatedFieldParams;
use bls12_381::fp::Fp as BlsFp;
use bls12_381::fp2::Fp2 as BlsFp2;
use bls12_381::{G2Affine, G2Projective};
use ff::PrimeFieldBits;
use num_bigint::BigInt;
use num_traits::{ToBytes, Zero};

use crate::curves::params::Bls12381G2Params;
use crate::fields::fp::{bigint_to_fpelem, Bls12381FpParams, FpElement};
use crate::fields::fp2::Fp2Element;

use super::params::EmulatedCurveParams;

#[derive(Clone)]
pub struct G2Point<F: PrimeFieldBits> {
    pub x: Fp2Element<F>,
    pub y: Fp2Element<F>,
}

impl<F> From<&G2Affine> for G2Point<F>
where
    F: PrimeFieldBits,
{
    fn from(value: &G2Affine) -> Self {
        let x = Fp2Element::<F>::from(&value.x);
        let y = Fp2Element::<F>::from(&value.y);
        Self { x, y }
    }
}

impl<F> From<&G2Point<F>> for G2Affine
where
    F: PrimeFieldBits,
{
    fn from(value: &G2Point<F>) -> Self {
        let x = BlsFp2::from(&value.x);
        let y = BlsFp2::from(&value.x);
        let z = if x.is_zero().into() && y.is_zero().into() {
            BlsFp2::zero()
        } else {
            BlsFp2::one()
        };
        let proj = G2Projective { x, y, z };
        Self::from(proj)
    }
}

impl<F: PrimeFieldBits> G2Point<F> {
    pub fn alloc_element<CS>(cs: &mut CS, value: &G2Affine) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // (0,0) is the point at infinity
        let x = Fp2Element::<F>::alloc_element(&mut cs.namespace(|| "allocate x (g2)"), &value.x)?;
        let y = Fp2Element::<F>::alloc_element(&mut cs.namespace(|| "allocate y (g2)"), &value.y)?;

        Ok(Self { x, y })
    }

    pub fn assert_is_equal<CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Fp2Element::<F>::assert_is_equal(&mut cs.namespace(|| "x =? x"), &a.x, &b.x)?;
        Fp2Element::<F>::assert_is_equal(&mut cs.namespace(|| "y =? y"), &a.y, &b.y)?;
        Ok(())
    }

    pub fn reduce<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x_reduced = self.x.reduce(&mut cs.namespace(|| "x mod P"))?;
        let y_reduced = self.y.reduce(&mut cs.namespace(|| "y mod P"))?;
        Ok(Self {
            x: x_reduced,
            y: y_reduced,
        })
    }

    pub fn assert_equality_to_constant<CS>(
        &self,
        cs: &mut CS,
        constant: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.x
            .assert_equality_to_constant(&mut cs.namespace(|| "x =? (const) x"), &constant.x)?;
        self.y
            .assert_equality_to_constant(&mut cs.namespace(|| "y =? (const) y"), &constant.y)?;
        Ok(())
    }

    /// Returns psi(P)
    pub fn psi<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self
            .x
            .conjugate(&mut cs.namespace(|| "x <- p.x.conjugate()"))?;
        let x = x.mul(&mut cs.namespace(|| "x <- x * c0"), &Bls12381G2Params::c0())?; // TODO: might be cheaper to use a different mul here since first coord is 0
        let y = self
            .y
            .conjugate(&mut cs.namespace(|| "y <- p.y.conjugate()"))?;
        let y = y.mul(&mut cs.namespace(|| "y <- y * c1"), &Bls12381G2Params::c1())?;
        Ok(Self { x, y })
    }

    /// Returns psi(psi(P))
    pub fn psi2<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let w = Fp2Element {
            a0: Bls12381G2Params::w(),
            a1: FpElement::zero(),
        }; // TODO: might be cheaper to use a different mul here since first coord is 0
        let x = self.x.mul(&mut cs.namespace(|| "x <- p.x * w"), &w)?;
        let y = self.y.neg(&mut cs.namespace(|| "y <- -p.y"))?;
        Ok(Self { x, y })
    }

    pub fn scalar_mul_by_seed<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let cs = &mut cs.namespace(|| "G2::scalar_mul_by_seed(q)");
        let z = self.triple(&mut cs.namespace(|| "z <- q.triple()"))?;
        let z = z.double(&mut cs.namespace(|| "z <- z.double()"))?;
        let z = z.double_and_add(&mut cs.namespace(|| "z <- z.double_and_add(q) 1"), self)?;
        let z = z.double_n(&mut cs.namespace(|| "z <- z.double_n(2)"), 2)?;
        let z = z.double_and_add(&mut cs.namespace(|| "z <- z.double_and_add(q) 2"), self)?;
        let z = z.double_n(&mut cs.namespace(|| "z <- z.double_n(8)"), 8)?;
        let z = z.double_and_add(&mut cs.namespace(|| "z <- z.double_and_add(q) 3"), self)?;
        let z = z.double_n(&mut cs.namespace(|| "z <- z.double_n(31)"), 31)?;
        let z = z.double_and_add(&mut cs.namespace(|| "z <- z.double_and_add(q) 4"), self)?;
        let z = z.double_n(&mut cs.namespace(|| "z <- z.double_n(16)"), 16)?;
        let z = z.neg(&mut cs.namespace(|| "z <- z.neg()"))?;

        Ok(z)
    }

    pub fn add<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (p, q) = (self, value);
        let cs = &mut cs.namespace(|| "G2::add(p, q)");
        // compute λ = (q.y-p.y)/(q.x-p.x)
        let qypy = q.y.sub(&mut cs.namespace(|| "qypy <- q.y - p.y"), &p.y)?;
        let qxpx = q.x.sub(&mut cs.namespace(|| "qxpx <- q.x - p.x"), &p.x)?;
        let lambda = qypy.div_unchecked(&mut cs.namespace(|| "lambda <- qypy div qxpx"), &qxpx)?;

        // xr = λ²-p.x-q.x
        let lambda_sq = lambda.square(&mut cs.namespace(|| "lambda_sq <- lambda.square()"))?;
        let qxpx = p.x.add(&mut cs.namespace(|| "qxpx <- p.x + q.x"), &q.x)?;
        let xr = lambda_sq.sub(&mut cs.namespace(|| "xr <- lambda_sq - qxpx"), &qxpx)?;

        // p.y = λ(p.x-r.x) - p.y
        let pxrx = p.x.sub(&mut cs.namespace(|| "pxrx <- p.x - xr"), &xr)?;
        let lambdapxrx = lambda.mul(&mut cs.namespace(|| "lambdapxrx <- lambda * pxrx"), &pxrx)?;
        let yr = lambdapxrx.sub(&mut cs.namespace(|| "yr <- lambdapxrx - p.y"), &p.y)?;

        Ok(Self { x: xr, y: yr })
    }

    pub fn add_or_double<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // NOTE: this is because the add function requires that p != q, otherwise it divides by zero
        // here we conditionally select between double or add, so this function ends up costing double
        // this is used in clear_cofactor() since there we don't know if the point is torsion free or not
        let diffx = self
            .x
            .sub(&mut cs.namespace(|| "diffx <- t1.x - t2.x"), &value.x)?;
        let diffy = self
            .y
            .sub(&mut cs.namespace(|| "diffy <- t1.y - t2.y"), &value.y)?;
        let is_eq_x = diffx.alloc_is_zero(&mut cs.namespace(|| "itfx <- diff.x ?= 0"))?;
        let is_eq_y = diffy.alloc_is_zero(&mut cs.namespace(|| "itfy <- diff.y ?= 0"))?;
        let is_eq = Boolean::and(
            &mut cs.namespace(|| "itf <- itfx & itfy"),
            &Boolean::Is(is_eq_x),
            &Boolean::Is(is_eq_y),
        )?;

        let double = self.double(&mut cs.namespace(|| "self.double()"))?;
        let double = double.reduce(&mut cs.namespace(|| "double.reduce()"))?;

        let value = value.reduce(&mut cs.namespace(|| "value.reduce()"))?;
        let dummy = Self {
            x: Fp2Element::zero(),
            y: Fp2Element::zero(),
        };
        let inputx = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "asdfx"),
            &value.x,
            &dummy.x,
            &is_eq,
        )?;
        let inputy = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "asdfy"),
            &value.y,
            &dummy.y,
            &is_eq,
        )?;
        let input = Self {
            x: inputx,
            y: inputy,
        };
        let add = self.add(&mut cs.namespace(|| "self.add()"), &input)?;
        let add = add.reduce(&mut cs.namespace(|| "add.reduce()"))?;

        let resx = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "asdfx2"),
            &add.x,
            &double.x,
            &is_eq,
        )?;
        let resy = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "asdfy2"),
            &add.y,
            &double.y,
            &is_eq,
        )?;

        Ok(Self { x: resx, y: resy })
    }

    pub fn neg<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Ok(Self {
            x: self.x.clone(),
            y: self.y.neg(&mut cs.namespace(|| "p <- p.g2_neg()"))?,
        })
    }

    pub fn sub<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let neg = value.neg(&mut cs.namespace(|| "q_neg <- q.neg()"))?;
        let res = self.add(&mut cs.namespace(|| "p + q_neg"), &neg)?;
        Ok(res)
    }

    pub fn double<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let p = self;
        let cs = &mut cs.namespace(|| "G2::double(p)");
        // compute λ = (3p.x²)/2*p.y
        let xx3a = p.x.square(&mut cs.namespace(|| "xx3a <- p.x.square()"))?;
        let xx3a = xx3a.mul_const(&mut cs.namespace(|| "xx3a <- xx3a * 3"), &BigInt::from(3))?;
        let y2 = p.y.double(&mut cs.namespace(|| "y2 <- p.y.double()"))?;
        let lambda = xx3a.div_unchecked(&mut cs.namespace(|| "lambda <- xx3a div y2"), &y2)?;

        // xr = λ²-2p.x
        let x2 = p.x.double(&mut cs.namespace(|| "x2 <- p.x.double()"))?;
        let lambda_sq = lambda.square(&mut cs.namespace(|| "lambda_sq <- lambda.square()"))?;
        let xr = lambda_sq.sub(&mut cs.namespace(|| "xr <- lambda_sq - x2"), &x2)?;

        // yr = λ(p-xr) - p.y
        let pxrx = p.x.sub(&mut cs.namespace(|| "pxrx <- p.x - xr"), &xr)?;
        let lambdapxrx = lambda.mul(&mut cs.namespace(|| "lambdapxrx <- lambda * pxrx"), &pxrx)?;
        let yr = lambdapxrx.sub(&mut cs.namespace(|| "yr <- lambdapxrx - p.y"), &p.y)?;

        Ok(Self { x: xr, y: yr })
    }

    pub fn double_n<CS>(&self, cs: &mut CS, n: usize) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut p: Option<&Self> = Some(self);
        let mut tmp: Option<Self> = None;
        let mut cs = cs.namespace(|| format!("G2::double_n(p, {n})"));
        for i in 0..n {
            if let Some(cur_p) = p {
                let val = cur_p.double(&mut cs.namespace(|| format!("p <- p.double() ({i})")))?;
                // TODO: This fails with an overflow without an explicit reduce call every few iterations, even though theoretically this should be happening automatically. needs further investigation
                // even weirder, the constraint count for `scalar_mul_by_seed` goes up if this reduce is called less often
                // currently this function is unused except for `scalar_mul_by_seed` which will be used for an `assert_is_on_g2` implementation
                let val = val.reduce(&mut cs.namespace(|| format!("p <- p.reduce() ({i})")))?;
                tmp = Some(val);
                p = tmp.as_ref();
            }
        }

        Ok(tmp.unwrap())
    }

    pub fn triple<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let p = self;
        let cs = &mut cs.namespace(|| "G2::triple(p)");
        // compute λ1 = (3p.x²)/2p.y
        let xx = p.x.square(&mut cs.namespace(|| "xx <- p.x.square()"))?;
        let xx = xx.mul_const(&mut cs.namespace(|| "xx <- xx * 3"), &BigInt::from(3))?;
        let y2 = p.y.double(&mut cs.namespace(|| "y2 <- p.y.double()"))?;
        let l1 = xx.div_unchecked(&mut cs.namespace(|| "l1 <- xx div y2"), &y2)?;

        // xr = λ1²-2p.x
        let x2 =
            p.x.mul_const(&mut cs.namespace(|| "x2 <- p.x * 2"), &BigInt::from(2))?;
        let l1l1 = l1.square(&mut cs.namespace(|| "l1l1 <- l1 * l1"))?;
        let x2 = l1l1.sub(&mut cs.namespace(|| "x2 <- l1l1 - x2"), &x2)?;

        // ommit y2 computation, and
        // compute λ2 = 2p.y/(x2 − p.x) − λ1.
        let x1x2 = p.x.sub(&mut cs.namespace(|| "x1x2 <- p.x - x2"), &x2)?;
        let l2 = y2.div_unchecked(&mut cs.namespace(|| "l2 <- y2 div x1x2"), &x1x2)?;
        let l2 = l2.sub(&mut cs.namespace(|| "l2 <- l2 - l1"), &l1)?;

        // xr = λ²-p.x-x2
        let l2l2 = l2.square(&mut cs.namespace(|| "l2l2 <- l2 * l2"))?;
        let qxrx = x2.add(&mut cs.namespace(|| "qxrx <- x2 + p.x"), &p.x)?;
        let xr = l2l2.sub(&mut cs.namespace(|| "xr <- l2l2 - qxrx"), &qxrx)?;

        // yr = λ(p.x-xr) - p.y
        let pxrx = p.x.sub(&mut cs.namespace(|| "pxrx <- p.x - xr"), &xr)?;
        let l2pxrx = l2.mul(&mut cs.namespace(|| "l2pxrx <- l2 * pxrx"), &pxrx)?;
        let yr = l2pxrx.sub(&mut cs.namespace(|| "yr <- l2pxrx - p.y"), &p.y)?;

        Ok(Self { x: xr, y: yr })
    }

    pub fn double_and_add<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (p, q) = (self, value);
        let cs = &mut cs.namespace(|| "G2::double_and_add(p, q)");
        // compute λ1 = (q.y-p.y)/(q.x-p.x)
        let yqyp = q.y.sub(&mut cs.namespace(|| "yqyp <- q.y - p.y"), &p.y)?;
        let xqxp = q.x.sub(&mut cs.namespace(|| "xqxp <- q.x - p.x"), &p.x)?;
        let l1 = yqyp.div_unchecked(&mut cs.namespace(|| "l1 <- yqyp div xqxp"), &xqxp)?;

        // compute x2 = l1²-p.x-q.x
        let l1l1 = l1.square(&mut cs.namespace(|| "l1l1 <- l1.square()"))?;
        let xqxp = p.x.add(&mut cs.namespace(|| "xqxp <- p.x + q.x"), &q.x)?;
        let x2 = l1l1.sub(&mut cs.namespace(|| "x2 <- l1l1 - xqxp"), &xqxp)?;

        // ommit y2 computation
        // compute l2 = -l1-2*p.y/(x2-p.x)
        let ypyp = p.y.add(&mut cs.namespace(|| "ypyp <- p.y + p.y"), &p.y)?;
        let x2xp = x2.sub(&mut cs.namespace(|| "x2xp <- x2 - p.x"), &p.x)?;
        let l2 = ypyp.div_unchecked(&mut cs.namespace(|| "l2 <- ypyp div x2xp"), &x2xp)?;
        let l2 = l1.add(&mut cs.namespace(|| "l2 <- l1 + l2"), &l2)?;
        let l2 = l2.neg(&mut cs.namespace(|| "l2 <- l2.neg()"))?;

        // compute x3 =l2²-p.x-x3
        let l2l2 = l2.square(&mut cs.namespace(|| "l2l2 <- l2.square()"))?;
        let x3 = l2l2.sub(&mut cs.namespace(|| "x3 <- l2l2 - p.x"), &p.x)?;
        let x3 = x3.sub(&mut cs.namespace(|| "x3 <- x3 - x2"), &x2)?;

        // compute y3 = l2*(p.x - x3)-p.y
        let y3 = p.x.sub(&mut cs.namespace(|| "y3 <- p.x - x3"), &x3)?;
        let y3 = l2.mul(&mut cs.namespace(|| "y3 <- l2 * y3"), &y3)?;
        let y3 = y3.sub(&mut cs.namespace(|| "y3 <- y3 - p.y"), &p.y)?;

        Ok(Self { x: x3, y: y3 })
    }

    pub fn opt_simple_swu2<CS>(cs: &mut CS, t: &Fp2Element<F>) -> Result<Self, SynthesisError>
    // TODO: this actually returns a point in E2' and not E2, so the type should be different
    where
        CS: ConstraintSystem<F>,
    {
        let cs = &mut cs.namespace(|| "G2::opt_simple_swu2(t)");

        let xi = Fp2Element::from_dec(("2", "1")).unwrap();
        let xi = xi.neg(&mut cs.namespace(|| "xi <- (-2, -1)"))?;

        // a = (0, 240)
        // b = (1012, 1012)
        let a = Fp2Element::from_dec(("0", "240")).unwrap();
        let a_a1_neg = a.a1.neg(&mut cs.namespace(|| "a_a1_neg <- -240"))?;
        let b = Fp2Element::from_dec(("1012", "1012")).unwrap();

        let t2 = t.square(&mut cs.namespace(|| "t2 <- t.square()"))?;
        let xi_t2 = xi.mul(&mut cs.namespace(|| "xi_t2 <- xi * t2"), &t2)?;
        let xi2_t4 = xi_t2.square(&mut cs.namespace(|| "xi2_t4 <- xi_t2.square()"))?;

        let num_den_common = xi2_t4.add(&mut cs.namespace(|| "ndc <- xi2_t4 + xi_t2"), &xi_t2)?;

        let x0_den_a0 = num_den_common
            .a1
            .mul(&mut cs.namespace(|| "x0_den_a0 <- ndc.a1 * a_a1"), &a.a1)?;
        let x0_den_a1 = num_den_common.a0.mul(
            &mut cs.namespace(|| "x0_den_a1 <- ndc.a0 * -a_a1"),
            &a_a1_neg,
        )?;
        let x0_den = Fp2Element {
            a0: x0_den_a0,
            a1: x0_den_a1,
        };
        let x0_den = x0_den.reduce(&mut cs.namespace(|| "x0_den <- x0_den.reduce()"))?;
        //  if X0_den = 0, replace with X1_den = a * xi; this way X1(t) = X0_num / X1_den = b / (xi * a)
        let is_den_0 = x0_den.alloc_is_zero(&mut cs.namespace(|| "is_den_0"))?;

        // X1_den = a * xi = 240 - 480 i
        let x1_den = Fp2Element::from_dec(("240", "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559307")).unwrap();

        let num_den_common =
            num_den_common.add(&mut cs.namespace(|| "ndc <- ndc + 1"), &Fp2Element::one())?;

        let tmp_ndc0 = b.a0.mul(
            &mut cs.namespace(|| "tmp_ndc0 <- b * ndc.a0"),
            &num_den_common.a0,
        )?;
        let tmp_ndc1 = b.a0.mul(
            &mut cs.namespace(|| "tmp_ndc1 <- b * ndx.a1"),
            &num_den_common.a1,
        )?;
        let x0_num_a0 = tmp_ndc0.sub(
            &mut cs.namespace(|| "x0_num_a0 <- tmp_ndc0 - tmp_ndc1"),
            &tmp_ndc1,
        )?;
        let x0_num_a1 = tmp_ndc0.add(
            &mut cs.namespace(|| "x0_num_a1 <- tmp_ndc0 + tmp_ndc1"),
            &tmp_ndc1,
        )?;
        let x0_num = Fp2Element {
            a0: x0_num_a0,
            a1: x0_num_a1,
        };

        let x0_den = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "x0_den <- select(x0_den, x1_den, is_den_0)"),
            &x0_den,
            &x1_den,
            &Boolean::Is(is_den_0),
        )?;

        let x0 = x0_num.div_unchecked(&mut cs.namespace(|| "x0 <- x0_num div x0_den"), &x0_den)?;

        // g(x) = x^3 + a x + b
        // Compute g(X0(t))
        let x0_2 = x0.square(&mut cs.namespace(|| "x0_2 <- x0.square()"))?;
        let x0_3 = x0_2.mul(&mut cs.namespace(|| "x0_3 <- x0_2 * x0"), &x0)?;
        let ax0 = x0.mul(&mut cs.namespace(|| "ax0 <- x0 * a"), &a)?;
        let gx0 = x0_3.add(&mut cs.namespace(|| "g <- x0_3 + b"), &b)?;
        let gx0 = gx0.add(&mut cs.namespace(|| "g <- g + ax0"), &ax0)?;

        // X1(t) = xi * t^2 * X0(t)
        let x1 = x0.mul(&mut cs.namespace(|| "x1 <- x0 * xi_t2"), &xi_t2)?;

        let xi3_t6 = xi2_t4.mul(&mut cs.namespace(|| "xi3_t6 <- xi2_t4 * xi_t2"), &xi_t2)?;
        // g(X1(t)) = xi^3 * t^6 * g(X0(t))
        let gx1 = xi3_t6.mul(&mut cs.namespace(|| "gx1 <- xi3_t6 * gx0"), &gx0)?;

        /*
        xi^3 is not a square, so one of gX0, gX1 must be a square
        isSquare = 1 if gX0 is a square, = 0 if gX1 is a square
        sqrt = sqrt(gX0) if isSquare = 1, sqrt = sqrt(gX1) if isSquare = 0

        Implementation is special to p^2 = 9 mod 16
        References:
        p. 9 of https://eprint.iacr.org/2019/403.pdf
        F.2.1.1 for general version for any field: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-14#appendix-F.2.1.1

        I do not use the trick for combining division and sqrt from Section 5 of
        Bernstein, Duif, Lange, Schwabe, and Yang, "High-speed high-security signatures",
        since division is cheap
         */

        // Precompute sqrt_candidate = gX0^{(p^2 + 7) / 16}
        // p^2 + 7
        let c1: BigInt = (Bls12381FpParams::modulus() * Bls12381FpParams::modulus()) + 7;
        // var c1[50] = long_add_unequal(n, 2*k, 1, prod(n, k, p, p), [7]);
        // (p^2 + 7) // 16
        let c2: BigInt = &c1 / BigInt::from(16);
        // var c2[2][50] = long_div2(n, 1, 2*k-1, c1, [16]);

        eprintln!("c2: {}", c2);

        // assert p^2 + 7 is divisible by 16
        assert_eq!(&c1 % 16, BigInt::zero(), "p^2 + 7 divisible by 16");

        // var sqrt_candidate[2][50] = find_Fp2_exp(n, k, gX0.out, p, c2[0]);
        // gX0^c2 in Fp2
        let gx0_n = BlsFp2::from(&gx0);
        let gx1_n = BlsFp2::from(&gx1);
        let c2_tmp = c2.to_le_bytes();
        let mut sqrt_candidate0 = BlsFp2::one();
        for e in c2_tmp.iter().rev() {
            for i in (0..8).rev() {
                sqrt_candidate0 = sqrt_candidate0.square();

                if ((*e >> i) & 1) == 1 {
                    sqrt_candidate0 *= gx0_n;
                }
            }
        }
        // let mut res = Self::one();
        // for e in by.iter().rev() {
        //     for i in (0..64).rev() {
        //         res = res.square();

        //         if ((*e >> i) & 1) == 1 {
        //             res *= self;
        //         }
        //     }
        // }
        // res
        // TODO: factor this ^ out and test it properly
        // let sqrt_candidate = gx0_n.pow_vartime(&c2_tmp.try_into().unwrap());

        // -1 is a square in Fp2 (because p^2 - 1 is even) so we only need to check half of the 8th roots of unity
        let tmp_big_to_fp2 = |c0: &str, c1: &str| -> BlsFp2 {
            let c0 = BigInt::parse_bytes(c0.as_bytes(), 10)
                .as_ref()
                .and_then(bigint_to_fpelem);
            let c1 = BigInt::parse_bytes(c1.as_bytes(), 10)
                .as_ref()
                .and_then(bigint_to_fpelem);
            if let (Some(c0), Some(c1)) = (c0, c1) {
                BlsFp2 { c0, c1 }
            } else {
                panic!()
            }
        };
        let tmp_big_to_fp = |v: &str| -> BlsFp {
            BigInt::parse_bytes(v.as_bytes(), 10)
                .as_ref()
                .and_then(bigint_to_fpelem)
                .expect("FIXME")
        };
        let tmp_big = |v: &str| -> BigInt { BigInt::parse_bytes(v.as_bytes(), 10).expect("FIXME") };
        let roots_of_unity = vec![
            tmp_big_to_fp2("1", "0"),
            tmp_big_to_fp2("0", "1"),
            tmp_big_to_fp2("1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257", "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257"),
            tmp_big_to_fp2("1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257", "2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530"),
        ];
        // sanity check
        for v in roots_of_unity.iter() {
            let mut s = v.clone();
            let mut asdf = 0;
            if s != BlsFp2::one() {
                asdf += 1;
                s *= v;
                if asdf > 4 {
                    panic!("{:?}^2 = {:?}\n{}", v, s, asdf);
                }
            }
        }
        let mut is_square0_val: bool = false;
        let mut sqrt_witness0: BlsFp2 = BlsFp2::zero();
        // if gX0 is a square, square root must be sqrt_candidate * (8th-root of unity)
        for root in roots_of_unity.iter() {
            let sqrt_tmp = sqrt_candidate0 * root;
            if sqrt_tmp * sqrt_tmp == gx0_n {
                is_square0_val = true;
                sqrt_witness0 = sqrt_tmp;
                break;
            }
        }
        let is_square0 = Boolean::from(AllocatedBit::alloc(
            &mut cs.namespace(|| "is_square0"),
            Some(is_square0_val),
        )?);

        // find square root of gX1
        // square root of gX1 must be = sqrt_candidate * t^3 * eta
        // for one of four precomputed values of eta
        // eta determined by eta^2 = xi^3 * (-1)^{-1/4}
        let t_native = BlsFp2::from(t);
        let t3 = t_native * t_native * t_native;
        let sqrt_candidate1 = sqrt_candidate0 * t3;

        let etas = vec![
            tmp_big_to_fp2("1015919005498129635886032702454337503112659152043614931979881174103627376789972962005013361970813319613593700736144", "1244231661155348484223428017511856347821538750986231559855759541903146219579071812422210818684355842447591283616181"),
            BlsFp2 { c0: bigint_to_fpelem(&(&Bls12381FpParams::modulus() - tmp_big("1244231661155348484223428017511856347821538750986231559855759541903146219579071812422210818684355842447591283616181"))).unwrap(), c1: tmp_big_to_fp("1015919005498129635886032702454337503112659152043614931979881174103627376789972962005013361970813319613593700736144") },
            tmp_big_to_fp2("1646015993121829755895883253076789309308090876275172350194834453434199515639474951814226234213676147507404483718679", "1637752706019426886789797193293828301565549384974986623510918743054325021588194075665960171838131772227885159387073"),
            BlsFp2 { c0: bigint_to_fpelem(&(&Bls12381FpParams::modulus() - tmp_big("1637752706019426886789797193293828301565549384974986623510918743054325021588194075665960171838131772227885159387073"))).unwrap(), c1: tmp_big_to_fp("1646015993121829755895883253076789309308090876275172350194834453434199515639474951814226234213676147507404483718679") },
        ];
        let mut is_square1_val: bool = false;
        let mut sqrt_witness1: BlsFp2 = BlsFp2::zero();
        for eta in etas.iter() {
            let sqrt_tmp = sqrt_candidate1 * eta;
            if sqrt_tmp * sqrt_tmp == gx1_n {
                is_square1_val = true;
                sqrt_witness1 = sqrt_tmp;
                break;
            }
        }

        assert!(
            is_square0_val || is_square1_val,
            "one of gX0 or gX1 must be a square"
        );
        let x0 = x0.reduce(&mut cs.namespace(|| "x0 <- x0.reduce()"))?;
        let x1 = x1.reduce(&mut cs.namespace(|| "x1 <- x1.reduce()"))?;

        // X = out[0] = X0 if isSquare == 1, else X = X1
        let outx = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "outx <- select(x1, x0, is_square0)"),
            &x1,
            &x0,
            &is_square0,
        )?;

        let sgn_t = t.sgn0(&mut cs.namespace(|| "sgn_t <- t.sgn0()"))?;
        let tmp_sgn0 = |x: &BlsFp2| -> bool {
            use bls12_381::hash_to_curve::Sgn0;
            x.sgn0().into()
        };

        let mut outy_val = if is_square0_val {
            sqrt_witness0
        } else {
            sqrt_witness1
        };
        if tmp_sgn0(&outy_val) != tmp_sgn0(&t_native) {
            outy_val = outy_val.neg(); // TODO: double check
        }
        let outy =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc outy <- outy_val"), &outy_val)?;

        // enforce that Y^2 = g(X)
        let y_sq = outy.square(&mut cs.namespace(|| "y_sq <- outy.square()"))?;
        let gx0 = gx0.reduce(&mut cs.namespace(|| "gx0 <- gx0.reduce()"))?;
        let gx1 = gx1.reduce(&mut cs.namespace(|| "gx1 <- gx1.reduce()"))?;
        let gx = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "gx <- select(gx1, gx0, is_square0)"),
            &gx1,
            &gx0,
            &is_square0,
        )?;
        Fp2Element::assert_is_equal(&mut cs.namespace(|| "y_sq == gx"), &y_sq, &gx)?;

        // sgn0(Y) == sgn0(t)
        let sgn_y = outy.sgn0(&mut cs.namespace(|| "sgn_y <- outy.sgn0()"))?;
        Boolean::enforce_equal(
            &mut cs.namespace(|| "sgn_y == sgn_t"),
            &Boolean::from(sgn_y),
            &Boolean::from(sgn_t),
        )?;

        Ok(Self { x: outx, y: outy })
    }

    // TODO: this takes and returns points in E2' and not E2
    pub fn iso3_map<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        /*
        3-Isogeny from E2' to E2
        References:
        Appendix E.3 of https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-14#appendix-E.3
        Section 4.3 of Wahby-Boneh: https://eprint.iacr.org/2019/403.pdf
        iso3(P) in Python reference code: https://github.com/algorand/bls_sigs_ref/blob/master/python-impl/opt_swu_g2.py
         */

        // Input:
        //  in = (x', y') point on E2' assumed to not be point at infinity
        //  inIsInfinity = 1 if input is point at infinity on E2' (in which case x', y' are arbitrary)
        // Output:
        //  out = (x, y) is point on E2 after applying 3-isogeny to in
        //  isInfinity = 1 if one of exceptional cases occurs and output should be point at infinity
        // Exceptions:
        //  inIsInfinity = 1
        //  input is a pole of the isogeny, i.e., x_den or y_den = 0

        // https://cfrg.github.io/draft-irtf-cfrg-hash-to-curve/draft-irtf-cfrg-hash-to-curve.html#appendix-E.3
        let iso3_coeffs = vec![
            vec![
                Fp2Element::from_dec(("889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542", "889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542")).unwrap(),
                Fp2Element::from_dec(("0", "2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522")).unwrap(),
                Fp2Element::from_dec(("2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526", "1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261")).unwrap(),
                Fp2Element::from_dec(("3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033", "0")).unwrap(),
            ],
            vec![
                Fp2Element::from_dec(("0", "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715")).unwrap(),
                Fp2Element::from_dec(("12", "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775")).unwrap(),
            ],
            vec![
                Fp2Element::from_dec(("3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558", "3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558")).unwrap(),
                Fp2Element::from_dec(("0", "889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518")).unwrap(),
                Fp2Element::from_dec(("2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524", "1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263")).unwrap(),
                Fp2Element::from_dec(("2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776", "0")).unwrap(),
            ],
            vec![
                Fp2Element::from_dec(("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355", "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355")).unwrap(),
                Fp2Element::from_dec(("0", "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571")).unwrap(),
                Fp2Element::from_dec(("18", "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769")).unwrap(),
            ],
        ];

        // x = x_num / x_den
        // y = y' * y_num / y_den
        // x_num = sum_{i=0}^3 coeffs[0][i] * x'^i
        // x_den = x'^2 + coeffs[1][1] * x' + coeffs[1][0]
        // y_num = sum_{i=0}^3 coeffs[2][i] * x'^i
        // y_den = x'^3 + sum_{i=0}^2 coeffs[3][i] * x'^i

        let xp1 = self.x.clone();
        let xp2 = self.x.square(&mut cs.namespace(|| "xp2 <- P.x.square()"))?;
        let xp3 = xp2.mul(&mut cs.namespace(|| "xp3 <- xp2 * P.x"), &self.x)?;
        let xp_pow = vec![xp1.clone(), xp2.clone(), xp3.clone()];
        let deg = vec![3, 1, 3, 2];
        let mut coeffs_xp = vec![];
        for i in 0..4 {
            let mut coeffs_j = vec![];
            for j in 0..deg[i] {
                let coeff = iso3_coeffs[i][j + 1].mul(
                    &mut cs.namespace(|| {
                        format!("coeff_xp_{i}_{j} <- coeffs[{i}][{}] * xp_pow[{j}]", j + 1)
                    }),
                    &xp_pow[j],
                )?;
                coeffs_j.push(coeff);
            }
            coeffs_xp.push(coeffs_j);
        }
        let mut x_frac = vec![];
        for i in 0..4 {
            let mut x_f = iso3_coeffs[i][0].clone();
            for j in 0..deg[i] {
                x_f = x_f.add(
                    &mut cs.namespace(|| format!("x_f_{i} <- x_f_{i} + coeff_xp_{i}_{j}")),
                    &coeffs_xp[i][j],
                )?;
            }
            x_frac.push(x_f);
        }
        x_frac[1] = x_frac[1].add(&mut cs.namespace(|| "x_f_1 <- x_f_1 + xp2"), &xp2)?;
        x_frac[3] = x_frac[3].add(&mut cs.namespace(|| "x_f_3 <- x_f_3 + xp3"), &xp3)?;

        let den_0 = x_frac[1].clone();
        let den_1 = x_frac[3].clone();
        let den_0_is_zero = den_0.alloc_is_zero(&mut cs.namespace(|| "den_0_is_zero"))?;
        let den_1_is_zero = den_1.alloc_is_zero(&mut cs.namespace(|| "den_1_is_zero"))?;
        let is_infinity = Boolean::or(
            &mut cs.namespace(|| "is_infinity <- or(den_0_is_zero, den_1_is_zero)"),
            &Boolean::from(den_0_is_zero),
            &Boolean::from(den_1_is_zero),
        )?;
        let den_0 = den_0.reduce(&mut cs.namespace(|| "den_0 <- den_0.reduce()"))?;
        let den_1 = den_1.reduce(&mut cs.namespace(|| "den_1 <- den_1.reduce()"))?;
        let den_0 = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "den_0 <- select(den_0, 0, is_infinity)"),
            &den_0,
            &Fp2Element::zero(),
            &is_infinity,
        )?;
        let den_1 = Fp2Element::conditionally_select(
            &mut cs.namespace(|| "den_1 <- select(den_1, 0, is_infinity)"),
            &den_1,
            &Fp2Element::zero(),
            &is_infinity,
        )?;

        let num_0 = x_frac[0].clone();
        let num_1 = x_frac[2].clone();

        // num / den if den != 0, else num / 1
        let x_0 = num_0.div_unchecked(&mut cs.namespace(|| "x_0 <- num_0 div den_0"), &den_0)?;
        let x_1 = num_1.div_unchecked(&mut cs.namespace(|| "x_1 <- num_1 div den_1"), &den_1)?;

        let y = self.y.mul(&mut cs.namespace(|| "y <- P.y * x_1"), &x_1)?;

        Ok(Self { x: x_0, y })
    }

    // in = P, a point on curve E2
    // out = [x^2 - x - 1]P + [x-1]*psi(P) + psi2(2*P)
    // where x = -15132376222941642752 is the parameter for BLS12-381
    pub fn clear_cofactor<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // from bls12_381:
        // self.double().psi2() // psi^2(2P)
        //     + (t1 + t2).mul_by_x() // psi^2(2P) + [x^2] P + [x] psi(P)
        //     - t1 // psi^2(2P) + [x^2 - x] P + [x] psi(P)
        //     - t2 // psi^2(2P) + [x^2 - x] P + [x - 1] psi(P)
        //     - self // psi^2(2P) + [x^2 - x - 1] P + [x - 1] psi(P)

        // TODO: currently this will divide by zero if P is torsion free (when t1 = t2)
        let t1 = self.scalar_mul_by_seed(&mut cs.namespace(|| "t1 <- p.scalar_mul_by_seed()"))?;
        let t2 = self.psi(&mut cs.namespace(|| "t2 <- p.psi()"))?;

        let z = self.double(&mut cs.namespace(|| "z <- p.double()"))?;
        let z = z.psi2(&mut cs.namespace(|| "z <- z.psi2()"))?;
        let t3 = t1.add_or_double(&mut cs.namespace(|| "t3 <- t1 + t2"), &t2)?;
        let t3 = t3.scalar_mul_by_seed(&mut cs.namespace(|| "t3 <- t3.scalar_mul_by_seed()"))?;
        let z = z.add_or_double(&mut cs.namespace(|| "z <- z + t3"), &t3)?;
        let z = z.sub(&mut cs.namespace(|| "z <- z - t1"), &t1)?;
        let z = z.sub(&mut cs.namespace(|| "z <- z - t2"), &t2)?;
        let z = z.sub(&mut cs.namespace(|| "z <- z - p"), self)?;

        Ok(z)
    }

    pub fn map_to_g2<CS>(
        cs: &mut CS,
        p1: &Fp2Element<F>,
        p2: &Fp2Element<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let u0 = Self::opt_simple_swu2(&mut cs.namespace(|| "u0 <- p1.opt_simple_swu2()"), p1)?;
        let u1 = Self::opt_simple_swu2(&mut cs.namespace(|| "u1 <- p2.opt_simple_swu2()"), p2)?;
        let z = u0.add(&mut cs.namespace(|| "z <- u0 + u1"), &u1)?;

        let z = z.iso3_map(&mut cs.namespace(|| "z <- z.iso3_map()"))?;

        let z = z.clear_cofactor(&mut cs.namespace(|| "z <- z.clear_cofactor()"))?;
        // TODO: ensure z is infinity if either of the previous 2 ops is infinity

        Ok(z)
    }

    pub fn assert_is_on_curve<CS>(&self, cs: &mut CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    /// Asserts that `psi(P) == [x]P`
    pub fn assert_subgroup_check<CS>(&self, cs: &mut CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // TODO: does it make sense for this function to return a bit instead of asserting?
        let a = self.psi(&mut cs.namespace(|| "a <- p.psi()"))?;
        let b = self.scalar_mul_by_seed(&mut cs.namespace(|| "b <- p.scalar_mul_by_seed()"))?;
        Self::assert_is_equal(&mut cs.namespace(|| "a == b"), &a, &b)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bls12_381::Scalar;
    use ff::Field;
    use num_bigint::Sign;
    use pasta_curves::group::Group;
    use pasta_curves::Fp;

    use expect_test::{expect, Expect};
    fn expect_eq(computed: usize, expected: &Expect) {
        expected.assert_eq(&computed.to_string());
    }

    #[test]
    fn test_random_add() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let b = G2Projective::random(&mut rng);
        let c = a + b;
        let a = G2Affine::from(a);
        let b = G2Affine::from(b);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a+b"), &b_alloc).unwrap();
        G2Point::assert_is_equal(&mut cs.namespace(|| "a+b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["9592"]);
        expect_eq(cs.num_constraints(), &expect!["9556"]);
    }

    #[test]
    fn test_random_neg() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let c = -a;
        let a = G2Affine::from(a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.neg(&mut cs.namespace(|| "a.neg()")).unwrap();
        G2Point::assert_is_equal(&mut cs.namespace(|| "a.neg() = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1084"]);
        expect_eq(cs.num_constraints(), &expect!["1048"]);
    }

    #[test]
    fn test_random_triple() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let c = a + a.double();
        let a = G2Affine::from(a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.triple(&mut cs.namespace(|| "a.triple()")).unwrap();
        G2Point::assert_is_equal(&mut cs.namespace(|| "a.triple() = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["16685"]);
        expect_eq(cs.num_constraints(), &expect!["16697"]);
    }

    #[test]
    fn test_random_double() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let c = a.double();
        let a = G2Affine::from(a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.double(&mut cs.namespace(|| "a.double()")).unwrap();
        G2Point::assert_is_equal(&mut cs.namespace(|| "a.double() = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["9605"]);
        expect_eq(cs.num_constraints(), &expect!["9593"]);
    }

    #[test]
    fn test_random_sub() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let b = G2Projective::random(&mut rng);
        let c = a - b;
        let a = G2Affine::from(a);
        let b = G2Affine::from(b);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-b"), &b_alloc).unwrap();
        G2Point::assert_is_equal(&mut cs.namespace(|| "a-b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["9592"]);
        expect_eq(cs.num_constraints(), &expect!["9556"]);
    }

    #[test]
    fn test_random_double_and_add() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let b = G2Projective::random(&mut rng);
        let c = a.double() + b;
        let a = G2Affine::from(a);
        let b = G2Affine::from(b);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc
            .double_and_add(&mut cs.namespace(|| "a.double_and_add(b)"), &b_alloc)
            .unwrap();
        G2Point::assert_is_equal(
            &mut cs.namespace(|| "a.double_and_add(b) = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["16720"]);
        expect_eq(cs.num_constraints(), &expect!["16708"]);
    }

    #[test]
    fn test_random_mul_by_seed() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let x0 = bls12_381::Scalar::from(15132376222941642752);
        let c = a * x0;
        let c = -c;
        let a = G2Affine::from(a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc
            .scalar_mul_by_seed(&mut cs.namespace(|| "a.mul_by_seed()"))
            .unwrap();
        G2Point::assert_is_equal(
            &mut cs.namespace(|| "a.mul_by_seed() = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["788217"]);
        expect_eq(cs.num_constraints(), &expect!["790797"]);
    }

    #[test]
    fn test_random_subgroup_check_positive() {
        let mut rng = rand::thread_rng();
        let n = Scalar::random(&mut rng);
        let a = G2Affine::from(G2Projective::generator() * n);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        a_alloc
            .assert_subgroup_check(&mut cs.namespace(|| "a.subgroup_check()"))
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["789813"]);
        expect_eq(cs.num_constraints(), &expect!["792417"]);
    }

    #[test]
    fn test_random_psi2() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let c = a.psi2();
        let a = G2Affine::from(a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.psi2(&mut cs.namespace(|| "a.psi2()")).unwrap();
        G2Point::assert_is_equal(&mut cs.namespace(|| "a.psi2() = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1882"]);
        expect_eq(cs.num_constraints(), &expect!["1846"]);
    }

    #[test]
    fn test_random_psi() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let c = a.psi();
        let a = G2Affine::from(a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.psi(&mut cs.namespace(|| "a.psi()")).unwrap();
        G2Point::assert_is_equal(&mut cs.namespace(|| "a.psi() = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["2704"]);
        expect_eq(cs.num_constraints(), &expect!["2668"]);
    }

    #[test]
    fn test_random_clear_cofactor_torsion_free_point() {
        let mut rng = rand::thread_rng();
        let a = G2Projective::random(&mut rng);
        let c = a.clear_cofactor();
        let a = G2Affine::from(a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc
            .clear_cofactor(&mut cs.namespace(|| "a.clear_cofactor()"))
            .unwrap();
        G2Point::assert_is_equal(
            &mut cs.namespace(|| "a.clear_cofactor() = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1747942"]);
        expect_eq(cs.num_constraints(), &expect!["1753876"]);
    }

    #[test]
    fn test_random_clear_cofactor_torsion_point() {
        use crate::curves::params::EmulatedCurveParams;
        let b = BlsFp2::from(&Bls12381G2Params::<Fp>::b());
        use rand::RngCore;
        let mut rng = rand::thread_rng();
        let mut random_point = || loop {
            let x = BlsFp2::random(&mut rng);
            let y = ((x.square() * x) + b).sqrt();
            if y.is_some().into() {
                let flip_sign = rng.next_u32() % 2 != 0;
                return G2Affine {
                    x,
                    y: if flip_sign { -y.unwrap() } else { y.unwrap() },
                    infinity: 0.into(),
                };
            }
        };
        let mut a = random_point();
        while a.is_torsion_free().into() {
            a = random_point();
        }
        let c = G2Projective::from(a).clear_cofactor();
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc
            .clear_cofactor(&mut cs.namespace(|| "a.clear_cofactor()"))
            .unwrap();
        G2Point::assert_is_equal(
            &mut cs.namespace(|| "a.clear_cofactor() = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1747942"]);
        expect_eq(cs.num_constraints(), &expect!["1753876"]);
    }

    #[test]
    fn test_random_subgroup_check_negative() {
        use crate::curves::params::EmulatedCurveParams;
        let b = BlsFp2::from(&Bls12381G2Params::<Fp>::b());
        use rand::RngCore;
        let mut rng = rand::thread_rng();
        let mut random_point = || loop {
            let x = BlsFp2::random(&mut rng);
            let y = ((x.square() * x) + b).sqrt();
            if y.is_some().into() {
                let flip_sign = rng.next_u32() % 2 != 0;
                return G2Affine {
                    x,
                    y: if flip_sign { -y.unwrap() } else { y.unwrap() },
                    infinity: 0.into(),
                };
            }
        };
        let mut a = random_point();
        while a.is_torsion_free().into() {
            a = random_point();
        }

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        a_alloc
            .assert_subgroup_check(&mut cs.namespace(|| "a.subgroup_check()"))
            .unwrap();
        assert!(!cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["789813"]);
        expect_eq(cs.num_constraints(), &expect!["792417"]);
    }

    #[test]
    fn test_random_opt_simple_swu2() {
        fn blsfp_to_bigint(value: BlsFp) -> BigInt {
            let bytes = value.to_bytes();
            assert!(bytes.len() == 48);
            BigInt::from_bytes_be(Sign::Plus, &bytes)
        }
        fn big_to_circ(v: BlsFp) -> String {
            let mut x = blsfp_to_bigint(v);
            let p = std::iter::repeat(BigInt::from(2))
                .take(55)
                .fold(BigInt::from(1), |acc, x| acc * x);
            let mut res = vec![];
            for _ in 0..7 {
                let limb = &x % &p;
                res.push(limb);
                x = &x / &p;
            }
            assert!(x == BigInt::from(0));
            res.into_iter()
                .map(|b| format!("{}", b))
                .collect::<Vec<_>>()
                .join(",")
        }
        // fn dump(v: &BlsFp) {

        // }
        // let mut rng = rand::thread_rng();
        use rand::SeedableRng;
        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        let a = BlsFp2::random(&mut rng);
        let c = bls12_381::hash_to_curve::map_g2::map_to_curve_simple_swu(&a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc =
            G2Point::opt_simple_swu2(&mut cs.namespace(|| "opt_simple_swu2(a)"), &a_alloc).unwrap();
        let res_val = G2Affine::from(&res_alloc);
        eprintln!("a: {:?}\nc: {:?}\nr: {:?}", a, c, res_val);
        eprintln!("a = [{},{}]", big_to_circ(a.c0), big_to_circ(a.c1));
        G2Point::assert_is_equal(
            &mut cs.namespace(|| "opt_simple_swu2(a) = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["2704"]);
        expect_eq(cs.num_constraints(), &expect!["2668"]);
    }

    #[test]
    fn test_random_iso3_map() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let a = bls12_381::hash_to_curve::map_g2::map_to_curve_simple_swu(&a); // this ensures a is in E2'
        let c = bls12_381::hash_to_curve::map_g2::iso_map(&a);
        let a = G2Affine::from(a);
        let c = G2Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc
            .iso3_map(&mut cs.namespace(|| "iso3_map(a)"))
            .unwrap();
        G2Point::assert_is_equal(
            &mut cs.namespace(|| "iso3_map(a) = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["57832"]);
        expect_eq(cs.num_constraints(), &expect!["58060"]);
    }

    // #[test]
    // fn test_random_map_to_g2() {
    //     let mut rng = rand::thread_rng();
    //     let x = BlsFp2::random(&mut rng);
    //     let y = BlsFp2::random(&mut rng);
    //     let c =

    //     let mut cs = TestConstraintSystem::<Fp>::new();
    //     let x_alloc = Fp2Element::alloc_element(&mut cs.namespace(|| "alloc x"), &x).unwrap();
    //     let y_alloc = Fp2Element::alloc_element(&mut cs.namespace(|| "alloc y"), &y).unwrap();
    //     let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
    //     let res_alloc = G2Point::map_to_g2(&mut cs.namespace(|| "map_to_g2(x, y)"), &x_alloc, &y_alloc).unwrap();
    //     G2Point::assert_is_equal(&mut cs.namespace(|| "map_to_g2(x, y) = c"), &res_alloc, &c_alloc)
    //         .unwrap();
    //     if !cs.is_satisfied() {
    //         eprintln!("{:?}", cs.which_is_unsatisfied())
    //     }
    //     assert!(cs.is_satisfied());
    //     expect_eq(cs.num_inputs(), &expect!["1"]);
    //     expect_eq(cs.scalar_aux().len(), &expect!["2704"]);
    //     expect_eq(cs.num_constraints(), &expect!["2668"]);
    // }
}
