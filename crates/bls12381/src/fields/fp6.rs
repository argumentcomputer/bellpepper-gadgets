use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::fp2::Fp2 as BlsFp2;
use bls12_381::fp6::Fp6 as BlsFp6;
use ff::PrimeFieldBits;

use super::fp2::Fp2Element;

#[derive(Clone)]
pub struct Fp6Element<F: PrimeFieldBits> {
    pub(crate) b0: Fp2Element<F>,
    pub(crate) b1: Fp2Element<F>,
    pub(crate) b2: Fp2Element<F>,
}

impl<F> From<&BlsFp6> for Fp6Element<F>
where
    F: PrimeFieldBits,
{
    fn from(value: &BlsFp6) -> Self {
        let b0 = Fp2Element::<F>::from(&value.c0);
        let b1 = Fp2Element::<F>::from(&value.c1);
        let b2 = Fp2Element::<F>::from(&value.c2);
        Self { b0, b1, b2 }
    }
}

impl<F> TryFrom<&Fp6Element<F>> for BlsFp6
where
    F: PrimeFieldBits,
{
    type Error = SynthesisError;

    fn try_from(value: &Fp6Element<F>) -> Result<Self, Self::Error> {
        let c0 = BlsFp2::try_from(&value.b0)?;
        let c1 = BlsFp2::try_from(&value.b1)?;
        let c2 = BlsFp2::try_from(&value.b2)?;
        Ok(Self { c0, c1, c2 })
    }
}

impl<F: PrimeFieldBits> Fp6Element<F> {
    pub fn zero() -> Self {
        Self {
            b0: Fp2Element::zero(),
            b1: Fp2Element::zero(),
            b2: Fp2Element::zero(),
        }
    }

    pub fn one() -> Self {
        Self {
            b0: Fp2Element::one(),
            b1: Fp2Element::zero(),
            b2: Fp2Element::zero(),
        }
    }

    pub fn alloc_element<CS>(cs: &mut CS, value: &Option<BlsFp6>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = value.map(|v| v.c0);
        let c1 = value.map(|v| v.c1);
        let c2 = value.map(|v| v.c2);
        let b0 = Fp2Element::<F>::alloc_element(&mut cs.namespace(|| "allocate b0"), &c0)?;
        let b1 = Fp2Element::<F>::alloc_element(&mut cs.namespace(|| "allocate b1"), &c1)?;
        let b2 = Fp2Element::<F>::alloc_element(&mut cs.namespace(|| "allocate b2"), &c2)?;

        Ok(Self { b0, b1, b2 })
    }

    pub fn assert_is_equal<CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Fp2Element::<F>::assert_is_equal(&mut cs.namespace(|| "b0 =? b0"), &a.b0, &b.b0)?;
        Fp2Element::<F>::assert_is_equal(&mut cs.namespace(|| "b1 =? b1"), &a.b1, &b.b1)?;
        Fp2Element::<F>::assert_is_equal(&mut cs.namespace(|| "b2 =? b2"), &a.b2, &b.b2)?;
        Ok(())
    }

    pub fn reduce<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let b0_reduced = self.b0.reduce(&mut cs.namespace(|| "b0 mod P"))?;
        let b1_reduced = self.b1.reduce(&mut cs.namespace(|| "b1 mod P"))?;
        let b2_reduced = self.b2.reduce(&mut cs.namespace(|| "b2 mod P"))?;
        Ok(Self {
            b0: b0_reduced,
            b1: b1_reduced,
            b2: b2_reduced,
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
        self.b0
            .assert_equality_to_constant(&mut cs.namespace(|| "b0 =? (const) b0"), &constant.b0)?;
        self.b1
            .assert_equality_to_constant(&mut cs.namespace(|| "b1 =? (const) b1"), &constant.b1)?;
        self.b2
            .assert_equality_to_constant(&mut cs.namespace(|| "b2 =? (const) b2"), &constant.b2)?;
        Ok(())
    }

    pub fn alloc_is_zero<CS>(&self, cs: &mut CS) -> Result<AllocatedBit, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z0 = self.b0.alloc_is_zero(&mut cs.namespace(|| "b0 =? 0"))?;
        let z1 = self.b1.alloc_is_zero(&mut cs.namespace(|| "b1 =? 0"))?;
        let z2 = self.b2.alloc_is_zero(&mut cs.namespace(|| "b2 =? 0"))?;

        let t0 = AllocatedBit::and(&mut cs.namespace(|| "and(z0, z1)"), &z0, &z1)?;
        AllocatedBit::and(&mut cs.namespace(|| "and(and(z0, z1), z2)"), &t0, &z2)
    }

    pub fn add<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let b0 = self.b0.add(&mut cs.namespace(|| "b0 + b0"), &value.b0)?;
        let b1 = self.b1.add(&mut cs.namespace(|| "b1 + b1"), &value.b1)?;
        let b2 = self.b2.add(&mut cs.namespace(|| "b2 + b2"), &value.b2)?;
        Ok(Self { b0, b1, b2 })
    }

    pub fn sub<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let b0 = self.b0.sub(&mut cs.namespace(|| "b0 - b0"), &value.b0)?;
        let b1 = self.b1.sub(&mut cs.namespace(|| "b1 - b1"), &value.b1)?;
        let b2 = self.b2.sub(&mut cs.namespace(|| "b2 - b2"), &value.b2)?;
        Ok(Self { b0, b1, b2 })
    }

    pub fn neg<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let b0 = self.b0.neg(&mut cs.namespace(|| "-b0"))?;
        let b1 = self.b1.neg(&mut cs.namespace(|| "-b1"))?;
        let b2 = self.b2.neg(&mut cs.namespace(|| "-b2"))?;
        Ok(Self { b0, b1, b2 })
    }

    pub fn mul<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (x, y) = (self, value);
        let mut cs = cs.namespace(|| "Fp6::mul(x,y)");
        let t0 = x.b0.mul(&mut cs.namespace(|| "t0 <- x.b0 * y.b0"), &y.b0)?;
        let t1 = x.b1.mul(&mut cs.namespace(|| "t1 <- x.b1 * y.b1"), &y.b1)?;
        let t2 = x.b2.mul(&mut cs.namespace(|| "t2 <- x.b2 * y.b2"), &y.b2)?;

        let c0 = x.b1.add(&mut cs.namespace(|| "c0 <- x.b1 + x.b2"), &x.b2)?;
        let tmp =
            y.b1.add(&mut cs.namespace(|| "tmp <- y.b1 + y.b2"), &y.b2)?;
        let c0 = c0.mul(&mut cs.namespace(|| "c0 <- c0 * tmp"), &tmp)?;
        let c0 = c0.sub(&mut cs.namespace(|| "c0 <- c0 - t1"), &t1)?;
        let c0 = c0.sub(&mut cs.namespace(|| "c0 <- c0 - t2"), &t2)?;
        let c0 = c0.mul_by_nonresidue(&mut cs.namespace(|| "c0 <- c0.mul_by_nonresidue()"))?;
        let c0 = c0.add(&mut cs.namespace(|| "c0 <- c0 + t0"), &t0)?;

        let c1 = x.b0.add(&mut cs.namespace(|| "c1 <- x.b0 + x.b1"), &x.b1)?;
        let tmp =
            y.b0.add(&mut cs.namespace(|| "tmp <- y.b0 + y.b1"), &y.b1)?;
        let c1 = c1.mul(&mut cs.namespace(|| "c1 <- c1 * tmp"), &tmp)?;
        let c1 = c1.sub(&mut cs.namespace(|| "c1 <- c1 - t0"), &t0)?;
        let c1 = c1.sub(&mut cs.namespace(|| "c1 <- c1 - t1"), &t1)?;
        let tmp = t2.mul_by_nonresidue(&mut cs.namespace(|| "tmp <- t2.mul_by_nonresidue()"))?;
        let c1 = c1.add(&mut cs.namespace(|| "c1 <- c1 + tmp"), &tmp)?;

        let tmp =
            x.b0.add(&mut cs.namespace(|| "tmp <- x.b0 + x.b2"), &x.b2)?;
        let c2 = y.b0.add(&mut cs.namespace(|| "c2 <- y.b0 + y.b2"), &y.b2)?;
        let c2 = c2.mul(&mut cs.namespace(|| "c2 <- c2 * tmp"), &tmp)?;
        let c2 = c2.sub(&mut cs.namespace(|| "c2 <- c2 - t0"), &t0)?;
        let c2 = c2.sub(&mut cs.namespace(|| "c2 <- c2 - t2"), &t2)?;
        let c2 = c2.add(&mut cs.namespace(|| "c2 <- c2 + t1"), &t1)?;

        Ok(Self {
            b0: c0,
            b1: c1,
            b2: c2,
        })
    }

    pub fn double<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let b0 = self.b0.double(&mut cs.namespace(|| "double b0"))?;
        let b1 = self.b1.double(&mut cs.namespace(|| "double b1"))?;
        let b2 = self.b2.double(&mut cs.namespace(|| "double b2"))?;
        Ok(Self { b0, b1, b2 })
    }

    pub fn square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self;
        let mut cs = cs.namespace(|| "Fp6::square(x)");
        let c4 = x.b0.mul(&mut cs.namespace(|| "c4 <- x.b0 * x.b1"), &x.b1)?;
        let c4 = c4.double(&mut cs.namespace(|| "c4 <- c4.double()"))?;
        let c5 = x.b2.square(&mut cs.namespace(|| "c5 <- x.b2.square()"))?;
        let c1 = c5.mul_by_nonresidue(&mut cs.namespace(|| "c1 <- c5.mul_by_nonresidue()"))?;
        let c1 = c1.add(&mut cs.namespace(|| "c1 <- c1 + c4"), &c4)?;
        let c2 = c4.sub(&mut cs.namespace(|| "c2 <- c4 - c5"), &c5)?;
        let c3 = x.b0.square(&mut cs.namespace(|| "c3 <- x.b0.square()"))?;
        let c4 = x.b0.sub(&mut cs.namespace(|| "c4 <- x.b0 - x.b1"), &x.b1)?;
        let c4 = c4.add(&mut cs.namespace(|| "c4 <- c4 + x.b2"), &x.b2)?;
        let c5 = x.b1.mul(&mut cs.namespace(|| "c5 <- x.b1 * x.b2"), &x.b2)?;
        let c5 = c5.double(&mut cs.namespace(|| "c5 <- c5.double()"))?;
        let c4 = c4.square(&mut cs.namespace(|| "c4 <- c4.square()"))?;
        let c0 = c5.mul_by_nonresidue(&mut cs.namespace(|| "c0 <- c5.mul_by_nonresidue()"))?;
        let c0 = c0.add(&mut cs.namespace(|| "c0 <- c0 + c3"), &c3)?;
        let z2 = c2.add(&mut cs.namespace(|| "z2 <- c2 + c4"), &c4)?;
        let z2 = z2.add(&mut cs.namespace(|| "z2 <- z2 + c5"), &c5)?;
        let z2 = z2.sub(&mut cs.namespace(|| "z2 <- z2 - c3"), &c3)?;
        let z0 = c0;
        let z1 = c1;

        Ok(Self {
            b0: z0,
            b1: z1,
            b2: z2,
        })
    }

    pub fn mul_by_e2<CS>(&self, cs: &mut CS, value: &Fp2Element<F>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z0 = self.b0.mul(&mut cs.namespace(|| "b0 * e2(x)"), value)?;
        let z1 = self.b1.mul(&mut cs.namespace(|| "b1 * e2(x)"), value)?;
        let z2 = self.b2.mul(&mut cs.namespace(|| "b2 * e2(x)"), value)?;
        Ok(Self {
            b0: z0,
            b1: z1,
            b2: z2,
        })
    }

    /// Equivalent to multiplying by sparse element Fp6(0, b1, b2)
    pub fn mul_by_12<CS>(
        &self,
        cs: &mut CS,
        b1: &Fp2Element<F>,
        b2: &Fp2Element<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self;
        let mut cs = cs.namespace(|| "Fp6::mul_by_12(x, b1, b2)");
        let t1 = x.b1.mul(&mut cs.namespace(|| "t1 <- x.b1 * b1"), b1)?;
        let t2 = x.b2.mul(&mut cs.namespace(|| "t2 <- x.b2 * b2"), b2)?;
        let c0 = x.b1.add(&mut cs.namespace(|| "c0 <- x.b1 + x.b2"), &x.b2)?;
        let tmp = b1.add(&mut cs.namespace(|| "tmp <- b1 + b2"), b2)?;
        let c0 = c0.mul(&mut cs.namespace(|| "c0 <- c0 * tmp"), &tmp)?;
        let c0 = c0.sub(&mut cs.namespace(|| "c0 <- c0 - t1"), &t1)?;
        let c0 = c0.sub(&mut cs.namespace(|| "c0 <- c0 - t2"), &t2)?;
        let c0 = c0.mul_by_nonresidue(&mut cs.namespace(|| "c0 <- c0.mul_by_nonresidue()"))?;
        let c1 = x.b0.add(&mut cs.namespace(|| "c1 <- x.b0 + x.b1"), &x.b1)?;
        let c1 = c1.mul(&mut cs.namespace(|| "c1 <- c1 * b1"), b1)?;
        let c1 = c1.sub(&mut cs.namespace(|| "c1 <- c1 - t1"), &t1)?;
        let tmp = t2.mul_by_nonresidue(&mut cs.namespace(|| "tmp <- t2.mul_by_nonresidue()"))?;
        let c1 = c1.add(&mut cs.namespace(|| "c1 <- c1 + tmp"), &tmp)?;
        let tmp =
            x.b0.add(&mut cs.namespace(|| "tmp <- x.b0 + x.b2"), &x.b2)?;
        let c2 = b2.mul(&mut cs.namespace(|| "c2 <- b2 * tmp"), &tmp)?;
        let c2 = c2.sub(&mut cs.namespace(|| "c2 <- c2 - t2"), &t2)?;
        let c2 = c2.add(&mut cs.namespace(|| "c2 <- c2 + t1"), &t1)?;

        Ok(Self {
            b0: c0,
            b1: c1,
            b2: c2,
        })
    }

    /// Equivalent to multiplying by sparse element Fp6(b0, 0, 0)
    pub fn mul_by_0<CS>(&self, cs: &mut CS, b0: &Fp2Element<F>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self;
        let mut cs = cs.namespace(|| "Fp6::mul_by_0(x, b0)");
        let a = x.b0.mul(&mut cs.namespace(|| "a <- x.b0 * b0"), b0)?;
        let tmp =
            x.b0.add(&mut cs.namespace(|| "tmp <- x.b0 + x.b2"), &x.b2)?;
        let t2 = b0.mul(&mut cs.namespace(|| "t2 <- b0 * tmp"), &tmp)?;
        let t2 = t2.sub(&mut cs.namespace(|| "t2 <- t2 - a"), &a)?;
        let tmp =
            x.b0.add(&mut cs.namespace(|| "tmp <- x.b0 + x.b1"), &x.b1)?;
        let t1 = b0.mul(&mut cs.namespace(|| "t1 <- b0 * tmp"), &tmp)?;
        let t1 = t1.sub(&mut cs.namespace(|| "t1 <- t1 - a"), &a)?;

        Ok(Self {
            b0: a,
            b1: t1,
            b2: t2,
        })
    }

    /// Equivalent to multiplying by sparse element Fp6(b0, b1, 0)
    pub fn mul_by_01<CS>(
        &self,
        cs: &mut CS,
        b0: &Fp2Element<F>,
        b1: &Fp2Element<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self;
        let mut cs = cs.namespace(|| "Fp6::mul_by_01(x, b0, b1)");
        let a = x.b0.mul(&mut cs.namespace(|| "a <- x.b0 * b0"), b0)?;
        let b = x.b1.mul(&mut cs.namespace(|| "b <- x.b1 * b1"), b1)?;
        let tmp =
            x.b1.add(&mut cs.namespace(|| "tmp <- x.b1 + x.b2"), &x.b2)?;
        let t0 = b1.mul(&mut cs.namespace(|| "t0 <- b1 * tmp"), &tmp)?;
        let t0 = t0.sub(&mut cs.namespace(|| "t0 <- t0 - b"), &b)?;
        let t0 = t0.mul_by_nonresidue(&mut cs.namespace(|| "t0 <- t0.mul_by_nonresidue()"))?;
        let t0 = t0.add(&mut cs.namespace(|| "t0 <- t0 + a"), &a)?;
        let tmp =
            x.b0.add(&mut cs.namespace(|| "tmp <- x.b0 + x.b2"), &x.b2)?;
        let t2 = b0.mul(&mut cs.namespace(|| "t2 <- b0 * tmp"), &tmp)?;
        let t2 = t2.sub(&mut cs.namespace(|| "t2 <- t2 - a"), &a)?;
        let t2 = t2.add(&mut cs.namespace(|| "t2 <- t2 + b"), &b)?;
        let t1 = b0.add(&mut cs.namespace(|| "t1 <- b0 + b1"), b1)?;
        let tmp =
            x.b0.add(&mut cs.namespace(|| "tmp <- x.b0 + x.b1"), &x.b1)?;
        let t1 = t1.mul(&mut cs.namespace(|| "t1 <- t1 * tmp"), &tmp)?;
        let t1 = t1.sub(&mut cs.namespace(|| "t1 <- t1 - a"), &a)?;
        let t1 = t1.sub(&mut cs.namespace(|| "t1 <- t1 - b"), &b)?;

        Ok(Self {
            b0: t0,
            b1: t1,
            b2: t2,
        })
    }

    pub fn mul_by_nonresidue<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (z2, z1, z0) = (&self.b1, &self.b0, &self.b2);
        let z0 = z0.mul_by_nonresidue(&mut cs.namespace(|| "Fp6::mul_by_nonresidue(x)"))?;
        Ok(Self {
            b0: z0,
            b1: z1.clone(),
            b2: z2.clone(),
        })
    }

    pub fn inverse<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let val = BlsFp6::try_from(self).ok();
        let inv = val.and_then(|val| {
            if val.is_zero().into() {
                eprintln!("Inverse of zero Fp6 element cannot be calculated");
                return None;
            }
            Some(val.invert().unwrap())
        });

        let inv_alloc = Self::alloc_element(&mut cs.namespace(|| "alloc inv"), &inv)?;

        // x*inv = 1
        let prod = inv_alloc.mul(&mut cs.namespace(|| "x*inv"), self)?;

        Self::assert_is_equal(&mut cs.namespace(|| "x*inv = 1 mod P"), &prod, &Self::one())?;

        Ok(inv_alloc)
    }

    pub fn div_unchecked<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // returns self/value (or x/y)

        let x = BlsFp6::try_from(self).ok();
        let y = BlsFp6::try_from(value).ok();
        let div = x.and_then(|x| {
            y.and_then(|y| {
                if y.is_zero().into() {
                    eprintln!("Division by zero Fp6 element cannot be calculated");
                    return None;
                }
                let y_inv = y.invert().unwrap();
                Some(y_inv * x)
            })
        });

        let div_alloc = Self::alloc_element(&mut cs.namespace(|| "alloc div"), &div)?;

        // y*div = x
        let prod = div_alloc.mul(&mut cs.namespace(|| "y*div"), value)?;
        Self::assert_is_equal(&mut cs.namespace(|| "y*div = x"), &prod, self)?;

        Ok(div_alloc)
    }

    pub fn conditionally_select<CS>(
        cs: &mut CS,
        z0: &Self,
        z1: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let b0 = Fp2Element::<F>::conditionally_select(
            &mut cs.namespace(|| "cond b0"),
            &z0.b0,
            &z1.b0,
            condition,
        )?;
        let b1 = Fp2Element::<F>::conditionally_select(
            &mut cs.namespace(|| "cond b1"),
            &z0.b1,
            &z1.b1,
            condition,
        )?;
        let b2 = Fp2Element::<F>::conditionally_select(
            &mut cs.namespace(|| "cond b2"),
            &z0.b2,
            &z1.b2,
            condition,
        )?;
        Ok(Self { b0, b1, b2 })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use halo2curves::bn256::Fq as Fp;

    use expect_test::{expect, Expect};
    fn expect_eq(computed: usize, expected: &Expect) {
        expected.assert_eq(&computed.to_string());
    }

    #[test]
    fn test_random_add() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let b = BlsFp6::random(&mut rng);
        let c = a + b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a+b"), &b_alloc).unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a+b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1500"]);
        expect_eq(cs.num_constraints(), &expect!["1398"]);
    }

    #[test]
    fn test_random_sub() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let b = BlsFp6::random(&mut rng);
        let c = a - b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-b"), &b_alloc).unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a-b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1500"]);
        expect_eq(cs.num_constraints(), &expect!["1398"]);
    }

    #[test]
    fn test_random_double() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let c = a + a;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.double(&mut cs.namespace(|| "2a")).unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "2a = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1458"]);
        expect_eq(cs.num_constraints(), &expect!["1398"]);
    }

    #[test]
    fn test_random_mul() {
        use std::ops::Mul;

        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let b = BlsFp6::random(&mut rng);
        let c = a.mul(b);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.mul(&mut cs.namespace(|| "a*b"), &b_alloc).unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["5125"]);
        expect_eq(cs.num_constraints(), &expect!["5035"]);
    }

    #[test]
    fn test_random_mul_by_nonresidue() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let c = a.mul_by_nonresidue();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .mul_by_nonresidue(&mut cs.namespace(|| "a*(1+u)"))
            .unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a*(1+u) = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1458"]);
        expect_eq(cs.num_constraints(), &expect!["1398"]);
    }

    #[test]
    fn test_random_square() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let c = a.square();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.square(&mut cs.namespace(|| "a²")).unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a² = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["5000"]);
        expect_eq(cs.num_constraints(), &expect!["4952"]);
    }

    #[test]
    fn test_random_div() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let mut b = BlsFp6::random(&mut rng);
        while b.invert().is_none().into() {
            b = BlsFp6::random(&mut rng);
        }
        let c = a * b.invert().unwrap();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .div_unchecked(&mut cs.namespace(|| "a div b"), &b_alloc)
            .unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a div b = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["6541"]);
        expect_eq(cs.num_constraints(), &expect!["6433"]);
    }

    #[test]
    fn test_random_mul_by_e2() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let b = BlsFp2::random(&mut rng);
        let c = a * BlsFp6::from(b);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = Fp2Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .mul_by_e2(&mut cs.namespace(|| "a*b (e2)"), &b_alloc)
            .unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["4805"]);
        expect_eq(cs.num_constraints(), &expect!["4743"]);
    }

    #[test]
    fn test_random_mul_by_0() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let b0 = BlsFp2::random(&mut rng);
        let b = BlsFp6 {
            c0: b0,
            c1: BlsFp2::zero(),
            c2: BlsFp2::zero(),
        };
        let c = a * b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b0_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc b0"), &Some(b0)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .mul_by_0(&mut cs.namespace(|| "a*b (e2)"), &b0_alloc)
            .unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["4845"]);
        expect_eq(cs.num_constraints(), &expect!["4783"]);
    }

    #[test]
    fn test_random_mul_by_12() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let b1 = BlsFp2::random(&mut rng);
        let b2 = BlsFp2::random(&mut rng);
        let b = BlsFp6 {
            c0: BlsFp2::zero(),
            c1: b1,
            c2: b2,
        };
        let c = a * b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b1_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc b1"), &Some(b1)).unwrap();
        let b2_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc b2"), &Some(b2)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .mul_by_12(&mut cs.namespace(|| "a*b (e2)"), &b1_alloc, &b2_alloc)
            .unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["5032"]);
        expect_eq(cs.num_constraints(), &expect!["4956"]);
    }

    #[test]
    fn test_random_mul_by_01() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let b0 = BlsFp2::random(&mut rng);
        let b1 = BlsFp2::random(&mut rng);
        let c = a.mul_by_01(&b0, &b1);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b0_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc b0"), &Some(b0)).unwrap();
        let b1_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc b1"), &Some(b1)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .mul_by_01(&mut cs.namespace(|| "a*b (e2)"), &b0_alloc, &b1_alloc)
            .unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["5022"]);
        expect_eq(cs.num_constraints(), &expect!["4946"]);
    }

    #[test]
    fn test_random_neg() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let c = -&a;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.neg(&mut cs.namespace(|| "-a")).unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "-a = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["1458"]);
        expect_eq(cs.num_constraints(), &expect!["1398"]);
    }

    #[test]
    fn test_random_inverse() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let c = a.invert().unwrap();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.inverse(&mut cs.namespace(|| "a^-1")).unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a^-1 = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["6499"]);
        expect_eq(cs.num_constraints(), &expect!["6433"]);
    }

    #[test]
    fn test_random_alloc_is_zero() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let b = BlsFp6::random(&mut rng);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-a"), &a_alloc).unwrap();
        let zero = Fp6Element::zero();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a-a = 0"), &res_alloc, &zero).unwrap();
        let zbit_alloc = res_alloc
            .alloc_is_zero(&mut cs.namespace(|| "z <- a-a ?= 0"))
            .unwrap();
        let cond_alloc = Fp6Element::conditionally_select(
            &mut cs.namespace(|| "select(a, b, z)"),
            &a_alloc,
            &b_alloc,
            &Boolean::Is(zbit_alloc),
        )
        .unwrap();
        Fp6Element::assert_is_equal(
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
        expect_eq(cs.scalar_aux().len(), &expect!["6659"]);
        expect_eq(cs.num_constraints(), &expect!["6689"]);
    }
}
