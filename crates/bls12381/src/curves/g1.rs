use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::G1Affine;
use bls12_381::{fp::Fp as BlsFp, G1Projective};
use ff::PrimeFieldBits;
use num_bigint::BigInt;

use crate::curves::params::Bls12381G1Params;
use crate::fields::fp::FpElement;

#[derive(Clone)]
pub struct G1Point<F: PrimeFieldBits> {
    pub x: FpElement<F>,
    pub y: FpElement<F>,
}

impl<F> From<&G1Affine> for G1Point<F>
where
    F: PrimeFieldBits,
{
    fn from(value: &G1Affine) -> Self {
        let x = FpElement::<F>::from(&value.x);
        let y = FpElement::<F>::from(&value.y);
        Self { x, y }
    }
}

impl<F> From<&G1Point<F>> for G1Affine
where
    F: PrimeFieldBits,
{
    fn from(value: &G1Point<F>) -> Self {
        let x = BlsFp::from(&value.x);
        let y = BlsFp::from(&value.x);
        let z = if x.is_zero().into() && y.is_zero().into() {
            BlsFp::zero()
        } else {
            BlsFp::one()
        };
        let proj = G1Projective { x, y, z };
        Self::from(proj)
    }
}

impl<F: PrimeFieldBits> G1Point<F> {
    pub fn identity() -> Self {
        // (0,0) is the point at infinity
        Self {
            x: FpElement::zero(),
            y: FpElement::zero(),
        }
    }

    pub fn alloc_element<CS>(cs: &mut CS, value: &G1Affine) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (x, y) = if value.is_identity().into() {
            (BlsFp::zero(), BlsFp::zero())
        } else {
            (value.x, value.y)
        };
        let x = FpElement::<F>::alloc_element(&mut cs.namespace(|| "allocate x (g1)"), &x)?;
        let y = FpElement::<F>::alloc_element(&mut cs.namespace(|| "allocate y (g1)"), &y)?;

        Ok(Self { x, y })
    }

    pub fn alloc_is_identity<CS>(&self, cs: &mut CS) -> Result<AllocatedBit, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self.x.alloc_is_zero(&mut cs.namespace(|| "x =? 0"))?;
        let y = self.y.alloc_is_zero(&mut cs.namespace(|| "y =? 0"))?;
        AllocatedBit::and(&mut cs.namespace(|| "and(x, y)"), &x, &y)
    }

    pub fn assert_is_equal<CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        FpElement::<F>::assert_is_equal(&mut cs.namespace(|| "x =? x"), &a.x, &b.x)?;
        FpElement::<F>::assert_is_equal(&mut cs.namespace(|| "y =? y"), &a.y, &b.y)?;
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

    pub fn phi<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self.x.mul(
            &mut cs.namespace(|| "x <- x * g1.w"),
            &Bls12381G1Params::w(),
        )?;
        Ok(Self {
            x,
            y: self.y.clone(),
        })
    }

    /// Asserts that `(y_a + y_c)*(x_b - x_a) - (y_b - y_a)*(x_a - x_c) = 0 mod p`.
    /// Used to show `a, b, -c` are all co-linear, or that `a + b = c`.
    /// Does not check that the points are on the curve or the proper subgroup.
    /// If `a == 0` or `b == 0`, enforces that `b == c` or `a == c` respectively. Does not work if `c == 0`
    pub fn assert_addition<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // compute leftside = (y_a + y_c) * (x_b - x_a)
        let aymcy = a.y.add(&mut cs.namespace(|| "aymcy <- a.y + c.y"), &c.y)?; // flip c.y to check for EC add
        let bxax = b.x.sub(&mut cs.namespace(|| "bxax <- b.x - a.x"), &a.x)?;
        let leftside = aymcy.mul(&mut cs.namespace(|| "leftside <- aymcy * bxax"), &bxax)?;

        // compute rightside = (y_b - y_a)*(x_a - x_c)
        let byay = b.y.sub(&mut cs.namespace(|| "byay <- b.y - a.y"), &a.y)?;
        let axcx = a.x.sub(&mut cs.namespace(|| "axcx <- a.x - c.x"), &c.x)?;
        let rightside = byay.mul(&mut cs.namespace(|| "rightside <- byay * axcx"), &axcx)?;

        let res = leftside.sub(
            &mut cs.namespace(|| "res <- leftside - rightside"),
            &rightside,
        )?;
        let res = res.alloc_is_zero(&mut cs.namespace(|| "res =? 0"))?;

        let aycy = a.y.sub(&mut cs.namespace(|| "aycy <- a.y - c.y"), &c.y)?;
        let bxcx = b.x.sub(&mut cs.namespace(|| "bxcx <- b.x - c.x"), &c.x)?;
        let bycy = b.y.sub(&mut cs.namespace(|| "bycy <- b.y - c.y"), &c.y)?;

        // if a == 0, then check b == c and ignore res
        let a_is_0 = a.alloc_is_identity(&mut cs.namespace(|| "a_is_0 <- a =? 0"))?;
        let bycy_is_0 = bycy.alloc_is_zero(&mut cs.namespace(|| "bycy_is_0 <- bycy =? 0"))?;
        let bxcx_is_0 = bxcx.alloc_is_zero(&mut cs.namespace(|| "bxcx_is_0 <- bxcx =? 0"))?;
        let b_eq_c = Boolean::and(
            &mut cs.namespace(|| "b_eq_c <- and(bxcx_is_0, bycy_is_0)"),
            &Boolean::from(bxcx_is_0),
            &Boolean::from(bycy_is_0),
        )?;
        let a_case = Boolean::and(
            &mut cs.namespace(|| "a_case <- and(a_is_0, b_eq_c)"),
            &Boolean::from(a_is_0.clone()),
            &b_eq_c,
        )?;
        // if b == 0, then check a == c and ignore res
        let b_is_0 = b.alloc_is_identity(&mut cs.namespace(|| "b_is_0 <- b =? 0"))?;
        let aycy_is_0 = aycy.alloc_is_zero(&mut cs.namespace(|| "aycy_is_0 <- aycy =? 0"))?;
        let axcx_is_0 = axcx.alloc_is_zero(&mut cs.namespace(|| "axcx_is_0 <- axcx =? 0"))?;
        let a_eq_c = Boolean::and(
            &mut cs.namespace(|| "a_eq_c <- and(axcx_is_0, aycy_is_0)"),
            &Boolean::from(axcx_is_0),
            &Boolean::from(aycy_is_0),
        )?;
        let b_case = Boolean::and(
            &mut cs.namespace(|| "b_case <- and(b_is_0, a_eq_c)"),
            &Boolean::from(b_is_0.clone()),
            &a_eq_c,
        )?;

        let any_is_0 = Boolean::or(
            &mut cs.namespace(|| "any_is_0 <- or(a_is_0, b_is_0)"),
            &Boolean::from(a_is_0),
            &Boolean::from(b_is_0),
        )?;

        // if any of the inputs is 0, then the collinear result bit needs to be cleared
        let res = Boolean::and(
            &mut cs.namespace(|| "res <- and(res, !any_is_0)"),
            &Boolean::from(res),
            &any_is_0.not(),
        )?;
        let res = Boolean::or(
            &mut cs.namespace(|| "res <- or(res, a_case)"),
            &res,
            &a_case,
        )?;
        let res = Boolean::or(
            &mut cs.namespace(|| "res <- or(res, b_case)"),
            &res,
            &b_case,
        )?;

        Boolean::enforce_equal(
            &mut cs.namespace(|| "enforce(res, true)"),
            &res,
            &Boolean::Constant(true),
        )?;

        Ok(())
    }

    pub fn add<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (p, q) = (self, value);
        let cs = &mut cs.namespace(|| "G1::add(p, q)");
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

    /// Returns the EC addition between `self` and `value`. Supports `p == q` and either point can be the identity
    /// It uses the unified formulas of Brier and Joye from [BriJoy02 (Corollary 1)](https://link.springer.com/content/pdf/10.1007/3-540-45664-3_24.pdf)
    pub fn add_unified<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (p, q) = (self, value);
        let cs = &mut cs.namespace(|| "G1::add_unified(p, q)");
        let sel1 = p.alloc_is_identity(&mut cs.namespace(|| "sel1 <- p.is_identity()"))?;
        let sel2 = q.alloc_is_identity(&mut cs.namespace(|| "sel2 <- q.is_identity()"))?;

        // λ = ((p.x+q.x)² - p.x*q.x + a)/(p.y + q.y)
        let pxqx = p.x.mul(&mut cs.namespace(|| "pxqx <- p.x * q.x"), &q.x)?;
        let pxplusqx =
            p.x.add(&mut cs.namespace(|| "pxplusqx <- p.x + q.x"), &q.x)?;
        let num = pxplusqx.square(&mut cs.namespace(|| "num <- pxplusqx^2"))?;
        let num = num.sub(&mut cs.namespace(|| "num <- num - pxqx"), &pxqx)?;
        let denum = p.y.add(&mut cs.namespace(|| "denum <- p.y + q.y"), &q.y)?;
        // if p.y + q.y = 0, assign dummy 1 to denum and continue
        let sel3 = denum.alloc_is_zero(&mut cs.namespace(|| "sel3 <- denum.is_zero()"))?;
        let denum = FpElement::conditionally_select(
            &mut cs.namespace(|| "denum <- select(denum, 1, sel3)"),
            &denum,
            &FpElement::one(),
            &Boolean::from(sel3.clone()),
        )?;
        let lambda = num.div_unchecked(&mut cs.namespace(|| "lamda <- num div denum"), &denum)?;

        // x = λ^2 - p.x - q.x
        let xr = lambda.square(&mut cs.namespace(|| "xr <- lambda.square()"))?;
        let xr = xr.sub(&mut cs.namespace(|| "xr <- xr - pxplusqx"), &pxplusqx)?;

        // y = λ(p.x - xr) - p.y
        let yr = p.x.sub(&mut cs.namespace(|| "yr <- p.x - xr"), &xr)?;
        let yr = yr.mul(&mut cs.namespace(|| "yr <- yr * lambda"), &lambda)?;
        let yr = yr.sub(&mut cs.namespace(|| "yr <- yr - p.y"), &p.y)?;
        let xr = xr.reduce(&mut cs.namespace(|| "xr <- xr.reduce()"))?;
        let yr = yr.reduce(&mut cs.namespace(|| "yr <- yr.reduce()"))?;
        let res = Self { x: xr, y: yr };

        // if p=(0,0) return q
        let res = Self::conditionally_select(
            &mut cs.namespace(|| "res <- select(res, q, sel1)"),
            &res,
            q,
            &Boolean::from(sel1),
        )?;
        // if q=(0,0) return p
        let res = Self::conditionally_select(
            &mut cs.namespace(|| "res <- select(res, p, sel2)"),
            &res,
            p,
            &Boolean::from(sel2),
        )?;
        // if p.y + q.y = 0, return (0, 0)
        let res = Self::conditionally_select(
            &mut cs.namespace(|| "res <- select(res, 0, sel3)"),
            &res,
            &Self::identity(),
            &Boolean::from(sel3),
        )?;

        Ok(res)
    }

    pub fn neg<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Ok(Self {
            x: self.x.clone(),
            y: self.y.neg(&mut cs.namespace(|| "p <- p.g1_neg()"))?,
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
        let cs = &mut cs.namespace(|| "G1::double(p)");
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

    pub fn triple<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let p = self;
        let cs = &mut cs.namespace(|| "G1::triple(p)");
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
        let cs = &mut cs.namespace(|| "G1::double_and_add(p, q)");
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

    pub fn conditionally_select<CS>(
        cs: &mut CS,
        p0: &Self,
        p1: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = FpElement::conditionally_select(
            &mut cs.namespace(|| "cond x"),
            &p0.x,
            &p1.x,
            condition,
        )?;
        let y = FpElement::conditionally_select(
            &mut cs.namespace(|| "cond y"),
            &p0.y,
            &p1.y,
            condition,
        )?;
        Ok(Self { x, y })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use pasta_curves::group::Group;
    use pasta_curves::Fp;

    use expect_test::{expect, Expect};
    fn expect_eq(computed: usize, expected: &Expect) {
        expected.assert_eq(&computed.to_string());
    }

    #[test]
    fn test_random_add() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let b = G1Projective::random(&mut rng);
        let c = a + b;
        let a = G1Affine::from(a);
        let b = G1Affine::from(b);
        let c = G1Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a+b"), &b_alloc).unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "a+b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["5063"]);
        expect_eq(cs.num_constraints(), &expect!["5051"]);
    }

    #[test]
    fn test_random_add_unified() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let b = G1Projective::random(&mut rng);
        let c = a + b;
        let d = a + a;
        let a = G1Affine::from(a);
        let b = G1Affine::from(b);
        let c = G1Affine::from(c);
        let d = G1Affine::from(d);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let d_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc d"), &d).unwrap();
        let z_alloc =
            G1Point::alloc_element(&mut cs.namespace(|| "alloc z"), &G1Affine::identity()).unwrap();
        let res1_alloc = a_alloc
            .add_unified(&mut cs.namespace(|| "a+b"), &b_alloc)
            .unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "a+b = c"), &res1_alloc, &c_alloc).unwrap();
        let res2_alloc = a_alloc
            .add_unified(&mut cs.namespace(|| "a+a"), &a_alloc)
            .unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "a+a = d"), &res2_alloc, &d_alloc).unwrap();
        let res3_alloc = a_alloc
            .add_unified(&mut cs.namespace(|| "a+0"), &z_alloc)
            .unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "a+0 = a"), &res3_alloc, &a_alloc).unwrap();
        let res4_alloc = z_alloc
            .add_unified(&mut cs.namespace(|| "0+a"), &a_alloc)
            .unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "0+a = a"), &res4_alloc, &a_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["28644"]);
        expect_eq(cs.num_constraints(), &expect!["28836"]);
    }

    #[test]
    fn test_assert_addition() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let b = G1Projective::random(&mut rng);
        let c = a + b;
        let a = G1Affine::from(a);
        let b = G1Affine::from(b);
        let c = G1Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        // alloc it so it's not a constant
        let z_alloc =
            G1Point::alloc_element(&mut cs.namespace(|| "alloc 0"), &G1Affine::identity()).unwrap();
        G1Point::assert_addition(
            &mut cs.namespace(|| "assert_addition(a, b, c)"),
            &a_alloc,
            &b_alloc,
            &c_alloc,
        )
        .unwrap();
        // test cases where a == 0 or b == 0
        G1Point::assert_addition(
            &mut cs.namespace(|| "assert_addition(a, 0, a)"),
            &a_alloc,
            &z_alloc,
            &a_alloc,
        )
        .unwrap();
        G1Point::assert_addition(
            &mut cs.namespace(|| "assert_addition(0, b, b)"),
            &z_alloc,
            &b_alloc,
            &b_alloc,
        )
        .unwrap();
        G1Point::assert_addition(
            &mut cs.namespace(|| "assert_addition(0, 0, 0)"),
            &z_alloc,
            &z_alloc,
            &z_alloc,
        )
        .unwrap();

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());

        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["15256"]);
        expect_eq(cs.num_constraints(), &expect!["15488"]);
    }

    #[test]
    fn test_random_neg() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let c = -a;
        let a = G1Affine::from(a);
        let c = G1Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.neg(&mut cs.namespace(|| "a.neg()")).unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "a.neg() = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["542"]);
        expect_eq(cs.num_constraints(), &expect!["524"]);
    }

    #[test]
    fn test_random_triple() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let c = a + a.double();
        let a = G1Affine::from(a);
        let c = G1Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.triple(&mut cs.namespace(|| "a.triple()")).unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "a.triple() = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["8894"]);
        expect_eq(cs.num_constraints(), &expect!["8912"]);
    }

    #[test]
    fn test_random_double() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let c = a.double();
        let a = G1Affine::from(a);
        let c = G1Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.double(&mut cs.namespace(|| "a.double()")).unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "a.double() = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["5068"]);
        expect_eq(cs.num_constraints(), &expect!["5068"]);
    }

    #[test]
    fn test_random_sub() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let b = G1Projective::random(&mut rng);
        let c = a - b;
        let a = G1Affine::from(a);
        let b = G1Affine::from(b);
        let c = G1Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-b"), &b_alloc).unwrap();
        G1Point::assert_is_equal(&mut cs.namespace(|| "a-b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["5063"]);
        expect_eq(cs.num_constraints(), &expect!["5051"]);
    }

    #[test]
    fn test_random_double_and_add() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let b = G1Projective::random(&mut rng);
        let c = a.double() + b;
        let a = G1Affine::from(a);
        let b = G1Affine::from(b);
        let c = G1Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc
            .double_and_add(&mut cs.namespace(|| "a.double_and_add(b)"), &b_alloc)
            .unwrap();
        G1Point::assert_is_equal(
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
        expect_eq(cs.scalar_aux().len(), &expect!["8913"]);
        expect_eq(cs.num_constraints(), &expect!["8919"]);
    }

    #[test]
    fn test_random_alloc_is_zero() {
        let mut rng = rand::thread_rng();
        let a = G1Affine::from(G1Projective::random(&mut rng));
        let b = G1Affine::from(G1Projective::random(&mut rng));

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let neg_a = a_alloc.neg(&mut cs.namespace(|| "-a")).unwrap();
        let res_alloc = a_alloc
            .add_unified(&mut cs.namespace(|| "a-a"), &neg_a)
            .unwrap();
        G1Point::assert_is_equal(
            &mut cs.namespace(|| "a-a = 0"),
            &res_alloc,
            &G1Point::identity(),
        )
        .unwrap();
        let zbit_alloc = res_alloc
            .alloc_is_identity(&mut cs.namespace(|| "z <- a-a ?= 0"))
            .unwrap();
        let cond_alloc = G1Point::conditionally_select(
            &mut cs.namespace(|| "select(a, b, z)"),
            &a_alloc,
            &b_alloc,
            &Boolean::Is(zbit_alloc),
        )
        .unwrap();
        G1Point::assert_is_equal(
            &mut cs.namespace(|| "select(a, b, z) = b"),
            &cond_alloc,
            &b_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["9015"]);
        expect_eq(cs.num_constraints(), &expect!["9078"]);
    }
}
