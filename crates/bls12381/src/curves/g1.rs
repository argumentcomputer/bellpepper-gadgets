use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::G1Affine;
use bls12_381::{fp::Fp as BlsFp, G1Projective};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigInt;

use crate::curves::params::Bls12381G1Params;
use crate::fields::fp::FpElement;

#[derive(Clone)]
pub struct G1Point<F: PrimeField + PrimeFieldBits> {
    pub x: FpElement<F>,
    pub y: FpElement<F>,
}

impl<F> From<&G1Affine> for G1Point<F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &G1Affine) -> Self {
        let x = FpElement::<F>::from(&value.x);
        let y = FpElement::<F>::from(&value.y);
        Self { x, y }
    }
}

impl<F> From<&G1Point<F>> for G1Affine
where
    F: PrimeField + PrimeFieldBits,
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

impl<F: PrimeField + PrimeFieldBits> G1Point<F> {
    pub fn alloc_element<CS>(cs: &mut CS, value: &G1Affine) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // (0,0) is the point at infinity
        let x = FpElement::<F>::alloc_element(&mut cs.namespace(|| "allocate x (g1)"), &value.x)?;
        let y = FpElement::<F>::alloc_element(&mut cs.namespace(|| "allocate y (g1)"), &value.y)?;

        Ok(Self { x, y })
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

    //Implements constraint: (y_a + y_c) * (x_b - x_a) - (y_b - y_a)*(x_a - x_c) = 0 mod p
    //used to show (x_a, y_a), (x_b, y_b), (x_c, -y_c) are co-linear
    pub fn assert_collinear<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let cs = &mut cs.namespace(|| "G1::assert_collinear(a, b, c)");

        // compute leftside = (y_a + y_c) * (x_b - x_a)
        let aycy = a.y.add(&mut cs.namespace(|| "aycy <- a.y + c.y"), &c.y)?;
        let bxax = b.x.sub(&mut cs.namespace(|| "bxax <- b.x - a.x"), &a.x)?;
        let leftside = aycy.mul(&mut cs.namespace(|| "leftside <- aycy * bxax"), &bxax)?;

        //compute rightside = (y_b - y_a)*(x_a - x_c)
        let byay = b.y.sub(&mut cs.namespace(|| "byay <- b.y - a.y"), &a.y)?;
        let axcx = a.x.sub(&mut cs.namespace(|| "axcx <- a.x - c.x"), &c.x)?;
        let rightside = byay.mul(&mut cs.namespace(|| "rightside <- byay * axcx"), &axcx)?;

        FpElement::assert_is_equal(
            &mut cs.namespace(|| "leftside =? rightside"),
            &leftside,
            &rightside,
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

    pub fn double_n<CS>(&self, cs: &mut CS, n: usize) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut p: Option<&Self> = Some(self);
        let mut tmp: Option<Self> = None;
        let mut cs = cs.namespace(|| format!("G1::double_n(p, {n})"));
        for i in 0..n {
            if let Some(cur_p) = p {
                let val = cur_p.double(&mut cs.namespace(|| format!("p <- p.double() ({i})")))?;
                // TODO: visit
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

    pub fn scalar_mul_by_seed_square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let cs = &mut cs.namespace(|| "G1::scalar_mul_by_seed_square(q)");
        let z = self.double(&mut cs.namespace(|| "z <- q.double()"))?;
        let z = self.add(&mut cs.namespace(|| "z <- q + z"), &z)?;
        let z = z.double(&mut cs.namespace(|| "z <- z.double()"))?;
        let z = z.double_and_add(&mut cs.namespace(|| "z <- z.double_and_add(q) 1"), self)?;
        let z = z.double_n(&mut cs.namespace(|| "z <- z.double_n(2)"), 2)?;
        let z = z.double_and_add(&mut cs.namespace(|| "z <- z.double_and_add(q) 2"), self)?;
        let z = z.double_n(&mut cs.namespace(|| "z <- z.double_n(8)"), 8)?;
        let z = z.double_and_add(&mut cs.namespace(|| "z <- z.double_and_add(q) 3"), self)?;
        let t0 = z.double(&mut cs.namespace(|| "t0 <- z.double()"))?;
        let t0 = z.add(&mut cs.namespace(|| "t0 <- z + t0"), &t0)?;
        let t0 = t0.double(&mut cs.namespace(|| "t0 <- t0.double()"))?;
        let t0 = t0.double_and_add(&mut cs.namespace(|| "t0 <- t0.double_and_add(z) 1"), &z)?;
        let t0 = t0.double_n(&mut cs.namespace(|| "t0 <- t0.double_n(2)"), 2)?;
        let t0 = t0.double_and_add(&mut cs.namespace(|| "t0 <- t0.double_and_add(z) 2"), &z)?;
        let t0 = t0.double_n(&mut cs.namespace(|| "t0 <- t0.double_n(8)"), 8)?;
        let t0 = t0.double_and_add(&mut cs.namespace(|| "t0 <- t0.double_and_add(z) 3"), &z)?;
        let t0 = t0.double_n(&mut cs.namespace(|| "t0 <- t0.double_n(31)"), 31)?;
        let z = t0.add(&mut cs.namespace(|| "z <- t0 + z"), &z)?;
        let z = z.double_n(&mut cs.namespace(|| "z <- z.double_n(32) 1"), 32)?;
        let z = z.double_and_add(&mut cs.namespace(|| "z <- z.double_and_add(q) 4"), self)?;
        let z = z.double_n(&mut cs.namespace(|| "z <- z.double_n(32) 2"), 32)?;

        Ok(z)
    }

    /// Asserts that `phi(P) == [-x^2]P`
    pub fn assert_subgroup_check<CS>(&self, cs: &mut CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // FIXME: not working -- the circom-pairing strategy and the gnark-crypto strategy seem different, should change this to the gnark approach
        let d = |x: &Self| {
            let tmp = G1Affine::from(x);
            eprintln!("-> {}", tmp);
        };
        d(self);
        // TODO: makes sense for this to return a bit instead of asserting?
        let a = self.phi(&mut cs.namespace(|| "a <- p.phi()"))?;
        d(&a);
        let b = self.scalar_mul_by_seed_square(
            &mut cs.namespace(|| "b <- p.scalar_mul_by_seed_square()"),
        )?;
        d(&b);
        let b = b.neg(&mut cs.namespace(|| "b <- -b"))?;
        d(&b);
        Self::assert_is_equal(&mut cs.namespace(|| "a == b"), &a, &b)?;
        Ok(())
    }

    pub fn assert_is_on_curve<CS>(&self, cs: &mut CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
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
    fn test_collinear() {
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
        G1Point::assert_collinear(
            &mut cs.namespace(|| "a+b-c = 0"),
            &a_alloc,
            &b_alloc,
            &c_alloc,
        )
        .unwrap();

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());

        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["728"]);
        expect_eq(cs.num_constraints(), &expect!["695"]);
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
    fn test_random_mul_by_seed_square() {
        let mut rng = rand::thread_rng();
        let a = G1Projective::random(&mut rng);
        let x0 = bls12_381::Scalar::from(15132376222941642752);
        let c = a * (x0 * x0);
        let a = G1Affine::from(a);
        let c = G1Affine::from(c);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc
            .scalar_mul_by_seed_square(&mut cs.namespace(|| "a.mul_by_seed_square()"))
            .unwrap();
        G1Point::assert_is_equal(
            &mut cs.namespace(|| "a.mul_by_seed_square() = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["815445"]);
        expect_eq(cs.num_constraints(), &expect!["818820"]);
    }

    // TODO
    // #[test]
    // fn test_random_subgroup_check() {
    //     let mut rng = rand::thread_rng();
    //     let n = Scalar::random(&mut rng);
    //     let a = G1Affine::from(G1Projective::generator() * n);

    //     let mut cs = TestConstraintSystem::<Fp>::new();
    //     let a_alloc = G1Point::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
    //     a_alloc
    //         .assert_subgroup_check(&mut cs.namespace(|| "a.subgroup_check()"))
    //         .unwrap();
    //     if !cs.is_satisfied() {
    //         eprintln!("{:?}", cs.which_is_unsatisfied())
    //     }
    //     assert!(cs.is_satisfied());
    //     expect_eq(cs.num_inputs(), &expect!["1"]);
    //     expect_eq(cs.scalar_aux().len(), &expect!["815445"]);
    //     expect_eq(cs.num_constraints(), &expect!["818820"]);
    // }

    // #[test]
    // fn test_random_subgroup_check_negative() {
    //     todo!();
    // }
}
