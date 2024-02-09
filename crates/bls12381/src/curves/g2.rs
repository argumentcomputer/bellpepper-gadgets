use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_emulated::field_element::EmulatedFieldParams;
use bls12_381::fp::Fp as BlsFp;
use bls12_381::fp2::Fp2 as BlsFp2;
use bls12_381::{G2Affine, G2Projective};
use ff::PrimeFieldBits;
use num_bigint::BigInt;

use crate::curves::params::Bls12381G2Params;
use crate::fields::fp::{Bls12381FpParams, FpElement};
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

        let a = Fp2Element::from_dec(("0", "240")).unwrap();
        let a = a.neg(&mut cs.namespace(|| "a <- (-0, -240)"))?;
        let b = Fp2Element::from_dec(("1012", "1012")).unwrap();

        let t2 = t.square(&mut cs.namespace(|| "t2 <- t.square()"))?;
        let xi_t2 = xi.mul(&mut cs.namespace(|| "xi_t2 <- xi * t2"), &t2)?;
        let xi2_t4 = xi_t2.square(&mut cs.namespace(|| "xi2_t4 <- xi_t2.square()"))?;

        let num_den_common = xi2_t4.add(&mut cs.namespace(|| "ndc <- xi2_t4 + xi_t2"), &xi_t2)?;

        let x0_den = a.mul(&mut cs.namespace(|| "x0_den <- a * ndc"), &num_den_common)?;
        let x0_den = x0_den.reduce(&mut cs.namespace(|| "x0_den <- x0_den.reduce()"))?; // TODO: check if needed
        //  if X0_den = 0, replace with X1_den = a * xi; this way X1(t) = X0_num / X1_den = b / (xi * a)
        let is_den_0 = x0_den.alloc_is_zero(&mut cs.namespace(|| "is_den_0"))?;

        let x1_den = Fp2Element::from_dec(("240", "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559307")).unwrap();

        let num_den_common = num_den_common.add(&mut cs.namespace(|| "ndc <- ndc + 1"), &Fp2Element::one())?;

        let x0_num = b.mul(&mut cs.namespace(|| "x0_num <- b * ndc"), &num_den_common)?;

        let x0_den = Fp2Element::conditionally_select(&mut cs.namespace(|| "x0_den <- select(x0_den, x1_den, is_den_0)"), &x0_den, &x1_den, &Boolean::Is(is_den_0))?;

        let x0 = x0_num.div_unchecked(&mut cs.namespace(|| "x0 <- x0_num div x0_den"), &x0_den)?;

        // g(x) = x^3 + a x + b
        // Compute g(X0(t))

        todo!()
    }

    // TODO: this takes and returns points in E2' and not E2
    pub fn iso3_map<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
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
    fn test_random_hash_to_g2() {
        todo!();
    }
}
