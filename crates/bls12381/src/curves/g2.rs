use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::fp2::Fp2 as BlsFp2;
use bls12_381::{G2Affine, G2Projective};
use ff::PrimeFieldBits;
use num_bigint::BigInt;

use crate::curves::params::Bls12381G2Params;
use crate::fields::fp2::Fp2Element;

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

    pub fn psi<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self.x.mul_element(
            &mut cs.namespace(|| "x <- x * g2.u1"),
            &Bls12381G2Params::u1(),
        )?;
        let y = self
            .y
            .conjugate(&mut cs.namespace(|| "y <- y.conjugate()"))?;
        let y = y.mul(
            &mut cs.namespace(|| "y <- y * g2.v"),
            &Bls12381G2Params::v(),
        )?;
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

    // NOTE: this test currently takes a few minutes to run, so it's commented out
    // #[test]
    // fn test_random_mul_by_seed() {
    //     let mut rng = rand::thread_rng();
    //     let a = G2Projective::random(&mut rng);
    //     let x0 = bls12_381::Scalar::from(15132376222941642752);
    //     let c = a * x0;
    //     let c = -c;
    //     let a = G2Affine::from(a);
    //     let c = G2Affine::from(c);

    //     let mut cs = TestConstraintSystem::<Fp>::new();
    //     let a_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
    //     let c_alloc = G2Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
    //     let res_alloc = a_alloc
    //         .scalar_mul_by_seed(&mut cs.namespace(|| "a.mul_by_seed()"))
    //         .unwrap();
    //     G2Point::assert_is_equal(
    //         &mut cs.namespace(|| "a.mul_by_seed() = c"),
    //         &res_alloc,
    //         &c_alloc,
    //     )
    //     .unwrap();
    //     if !cs.is_satisfied() {
    //         eprintln!("{:?}", cs.which_is_unsatisfied())
    //     }
    //     assert!(cs.is_satisfied());
    //     expect_eq(cs.num_inputs(), expect!["1"]);
    //     expect_eq(cs.scalar_aux().len(), expect!["788217"]);
    //     expect_eq(cs.num_constraints(), expect!["790797"]);
    // }
}
