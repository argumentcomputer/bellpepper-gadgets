use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::fp12::Fp12 as BlsFp12;
use bls12_381::fp6::Fp6 as BlsFp6;
use ff::PrimeFieldBits;

use super::fp2::Fp2Element;
use super::fp6::Fp6Element;

#[derive(Clone)]
pub struct Fp12Element<F: PrimeFieldBits> {
    pub(crate) c0: Fp6Element<F>,
    pub(crate) c1: Fp6Element<F>,
}

impl<F> From<&BlsFp12> for Fp12Element<F>
where
    F: PrimeFieldBits,
{
    fn from(value: &BlsFp12) -> Self {
        let c0 = Fp6Element::<F>::from(&value.c0);
        let c1 = Fp6Element::<F>::from(&value.c1);
        Self { c0, c1 }
    }
}

impl<F> TryFrom<&Fp12Element<F>> for BlsFp12
where
    F: PrimeFieldBits,
{
    type Error = SynthesisError;

    fn try_from(value: &Fp12Element<F>) -> Result<Self, Self::Error> {
        let c0 = BlsFp6::try_from(&value.c0)?;
        let c1 = BlsFp6::try_from(&value.c1)?;
        Ok(Self { c0, c1 })
    }
}

impl<F: PrimeFieldBits> Fp12Element<F> {
    pub fn zero() -> Self {
        Self {
            c0: Fp6Element::zero(),
            c1: Fp6Element::zero(),
        }
    }

    pub fn one() -> Self {
        Self {
            c0: Fp6Element::one(),
            c1: Fp6Element::zero(),
        }
    }

    pub fn alloc_element<CS>(cs: &mut CS, value: &Option<BlsFp12>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let vc0 = value.map(|v| v.c0);
        let vc1 = value.map(|v| v.c1);
        let c0 = Fp6Element::<F>::alloc_element(&mut cs.namespace(|| "allocate c0"), &vc0)?;
        let c1 = Fp6Element::<F>::alloc_element(&mut cs.namespace(|| "allocate c1"), &vc1)?;

        Ok(Self { c0, c1 })
    }

    pub fn assert_is_equal<CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Fp6Element::<F>::assert_is_equal(&mut cs.namespace(|| "c0 =? c0"), &a.c0, &b.c0)?;
        Fp6Element::<F>::assert_is_equal(&mut cs.namespace(|| "c1 =? c1"), &a.c1, &b.c1)?;
        Ok(())
    }

    pub fn reduce<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0_reduced = self.c0.reduce(&mut cs.namespace(|| "c0 mod P"))?;
        let c1_reduced = self.c1.reduce(&mut cs.namespace(|| "c1 mod P"))?;
        Ok(Self {
            c0: c0_reduced,
            c1: c1_reduced,
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
        self.c0
            .assert_equality_to_constant(&mut cs.namespace(|| "c0 =? (const) c0"), &constant.c0)?;
        self.c1
            .assert_equality_to_constant(&mut cs.namespace(|| "c1 =? (const) c1"), &constant.c1)?;
        Ok(())
    }

    pub fn alloc_is_zero<CS>(&self, cs: &mut CS) -> Result<AllocatedBit, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z0 = self.c0.alloc_is_zero(&mut cs.namespace(|| "c0 =? 0"))?;
        let z1 = self.c1.alloc_is_zero(&mut cs.namespace(|| "c1 =? 0"))?;

        AllocatedBit::and(&mut cs.namespace(|| "and(z0, z1)"), &z0, &z1)
    }

    pub fn add<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.add(&mut cs.namespace(|| "c0 + c0"), &value.c0)?;
        let c1 = self.c1.add(&mut cs.namespace(|| "c1 + c1"), &value.c1)?;
        Ok(Self { c0, c1 })
    }

    pub fn sub<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.sub(&mut cs.namespace(|| "c0 - c0"), &value.c0)?;
        let c1 = self.c1.sub(&mut cs.namespace(|| "c1 - c1"), &value.c1)?;
        Ok(Self { c0, c1 })
    }

    pub fn conjugate<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z1 = self.c1.neg(&mut cs.namespace(|| "Fp12::conjugate()"))?;
        Ok(Self {
            c0: self.c0.clone(),
            c1: z1,
        })
    }

    pub fn mul<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (x, y) = (self, value);
        let mut cs = cs.namespace(|| "Fp12::mul(x,y)");
        let a = x.c0.add(&mut cs.namespace(|| "a <- x.c0 + x.c1"), &x.c1)?;
        let b = y.c0.add(&mut cs.namespace(|| "b <- y.c0 + y.c1"), &y.c1)?;
        let a = a.mul(&mut cs.namespace(|| "a <- a * b"), &b)?;
        let b = x.c0.mul(&mut cs.namespace(|| "b <- x.c0 * y.c0"), &y.c0)?;
        let c = x.c1.mul(&mut cs.namespace(|| "c <- x.c1 * y.c1"), &y.c1)?;
        let z1 = a.sub(&mut cs.namespace(|| "z1 <- a - b"), &b)?;
        let z1 = z1.sub(&mut cs.namespace(|| "z1 <- z1 - c"), &c)?;
        let z0 = c.mul_by_nonresidue(&mut cs.namespace(|| "z0 <- c.mul_by_nonresidue()"))?;
        let z0 = z0.add(&mut cs.namespace(|| "z0 <- z0 + b"), &b)?;

        Ok(Self { c0: z0, c1: z1 })
    }

    /// MulBy014 multiplies z by an Fp12 sparse element of the form
    ///
    ///  Fp12{
    ///    C0: Fp6{B0: c0, B1: c1, B2: 0},
    ///    C1: Fp6{B0: 0, B1: 1, B2: 0},
    ///  }
    pub fn mul_by_014<CS>(
        &self,
        cs: &mut CS,
        c0: &Fp2Element<F>,
        c1: &Fp2Element<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z = self;
        let mut cs = cs.namespace(|| "Fp12::mul_by_014(c0, c1)");

        let a =
            z.c0.mul_by_01(&mut cs.namespace(|| "a <- z.c0.mul_by_01(c0, c1)"), c0, c1)?;

        let b = Fp6Element {
            b0: z
                .c1
                .b2
                .mul_by_nonresidue(&mut cs.namespace(|| "b.b0 <- z.c1.b2.mul_by_nonresidue()"))?,
            b1: z.c1.b0.clone(),
            b2: z.c1.b1.clone(),
        };

        let d = c1.add(&mut cs.namespace(|| "d <- c1 + 1"), &Fp2Element::one())?;

        let rc1 =
            z.c1.add(&mut cs.namespace(|| "rc1 <- z.c1 + z.c0"), &z.c0)?;
        let rc1 = rc1.mul_by_01(&mut cs.namespace(|| "rc1 <- rc1.mul_by_01(c0, d)"), c0, &d)?;
        let rc1 = rc1.sub(&mut cs.namespace(|| "rc1 <- rc1 - a"), &a)?;
        let rc1 = rc1.sub(&mut cs.namespace(|| "rc1 <- rc1 - b"), &b)?;
        let rc0 = b.mul_by_nonresidue(&mut cs.namespace(|| "rc0 <- b.mul_by_nonresidue()"))?;
        let rc0 = rc0.add(&mut cs.namespace(|| "rc0 <- rc0 + a"), &a)?;

        Ok(Self { c0: rc0, c1: rc1 })
    }

    ///  mul_014_by_014 multiplies two Fp12 sparse element of the form:
    ///
    ///  Fp12{
    ///    C0: Fp6{B0: c0, B1: c1, B2: 0},
    ///    C1: Fp6{B0: 0, B1: 1, B2: 0},
    ///  }
    ///
    /// and
    ///
    ///  Fp12{
    ///    C0: Fp6{B0: d0, B1: d1, B2: 0},
    ///    C1: Fp6{B0: 0, B1: 1, B2: 0},
    ///  }
    pub fn mul_014_by_014<CS>(
        cs: &mut CS,
        c0: &Fp2Element<F>,
        c1: &Fp2Element<F>,
        d0: &Fp2Element<F>,
        d1: &Fp2Element<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut cs = cs.namespace(|| "Fp12::mul_014_by_014(c0, c1, d0, d1)");
        let one = Fp2Element::<F>::one();
        let x0 = c0.mul(&mut cs.namespace(|| "x0 <- c0 * d0"), d0)?;
        let x1 = c1.mul(&mut cs.namespace(|| "x1 <- c1 * d1"), d1)?;
        let tmp = c0.add(&mut cs.namespace(|| "tmp <- c0 + 1"), &one)?;
        let x04 = d0.add(&mut cs.namespace(|| "x04 <- d0 + 1"), &one)?;
        let x04 = x04.mul(&mut cs.namespace(|| "x04 <- x04 * tmp"), &tmp)?;
        let x04 = x04.sub(&mut cs.namespace(|| "x04 <- x04 - x0"), &x0)?;
        let x04 = x04.sub(&mut cs.namespace(|| "x04 <- x04 - 1"), &one)?;
        let tmp = c0.add(&mut cs.namespace(|| "tmp <- c0 + c1"), c1)?;
        let x01 = d0.add(&mut cs.namespace(|| "x01 <- d0 + d1"), d1)?;
        let x01 = x01.mul(&mut cs.namespace(|| "x01 <- x01 * tmp"), &tmp)?;
        let x01 = x01.sub(&mut cs.namespace(|| "x01 <- x01 - x0"), &x0)?;
        let x01 = x01.sub(&mut cs.namespace(|| "x01 <- x01 - x1"), &x1)?;
        let tmp = c1.add(&mut cs.namespace(|| "tmp <- c1 + 1"), &one)?;
        let x14 = d1.add(&mut cs.namespace(|| "x14 < - d1 + 1"), &one)?;
        let x14 = x14.mul(&mut cs.namespace(|| "x14 <- x14 * tmp"), &tmp)?;
        let x14 = x14.sub(&mut cs.namespace(|| "x14 <- x14 - x1"), &x1)?;
        let x14 = x14.sub(&mut cs.namespace(|| "x14 <- x14 - 1"), &one)?;

        let zc0b0 = Fp2Element::<F>::non_residue();
        let zc0b0 = zc0b0.add(&mut cs.namespace(|| "zc0b0 <- non_residue() + x0"), &x0)?;

        Ok(Self {
            c0: Fp6Element {
                b0: zc0b0,
                b1: x01,
                b2: x1,
            },
            c1: Fp6Element {
                b0: Fp2Element::zero(),
                b1: x04,
                b2: x14,
            },
        })
    }

    /// mul_by_01245 multiplies z by an Fp12 sparse element of the form
    ///
    ///  Fp12{
    ///    C0: Fp6{B0: c00, B1: c01, B2: c02},
    ///    C1: Fp6{B0: 0, B1: c11, B2: c12},
    ///  }
    pub fn mul_by_01245<CS>(
        &self,
        cs: &mut CS,
        c00: &Fp2Element<F>,
        c01: &Fp2Element<F>,
        c02: &Fp2Element<F>,
        c11: &Fp2Element<F>,
        c12: &Fp2Element<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z = self;
        let c0 = Fp6Element {
            b0: c00.clone(),
            b1: c01.clone(),
            b2: c02.clone(),
        };
        let c1 = Fp6Element {
            b0: Fp2Element::zero(),
            b1: c11.clone(),
            b2: c12.clone(),
        };
        let mut cs = cs.namespace(|| "Fp12::mul_by_01245(x, Fp12(c0,c1))");
        let a = z.c0.add(&mut cs.namespace(|| "a <- z.c0 + z.c1"), &z.c1)?;
        let b = c0.add(&mut cs.namespace(|| "b <- c0 + c1"), &c1)?;
        let a = a.mul(&mut cs.namespace(|| "a <- a * b"), &b)?;
        let b = z.c0.mul(&mut cs.namespace(|| "b <- z.c0 * c0"), &c0)?;
        let c = z.c1.mul_by_12(
            &mut cs.namespace(|| "c <- z.c1.mul_by_12(c11, c12)"),
            c11,
            c12,
        )?;
        let z1 = a.sub(&mut cs.namespace(|| "z1 <- a - b"), &b)?;
        let z1 = z1.sub(&mut cs.namespace(|| "z1 <- z1 - c"), &c)?;
        let z0 = c.mul_by_nonresidue(&mut cs.namespace(|| "z0 <- c.mul_by_nonresidue()"))?;
        let z0 = z0.add(&mut cs.namespace(|| "z0 <- z0 + b"), &b)?;

        Ok(Self { c0: z0, c1: z1 })
    }

    pub fn square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut cs = cs.namespace(|| "Fp12::square(x)");

        // This explicit reduction is single-handedly responsible for saving
        // millions of constraints during a pairing operation. This function is
        // repeatedly called inside `miller_loop_lines`, and is responsible for
        // a considerable chunk of the constraints
        let x = self.reduce(&mut cs.namespace(|| "x <- x.reduce()"))?;

        let c0 = x.c0.sub(&mut cs.namespace(|| "c0 <- x.c0 - x.c1"), &x.c1)?;
        let c3 =
            x.c1.mul_by_nonresidue(&mut cs.namespace(|| "c3 <- x.c1.mul_by_nonresidue()"))?;
        let c3 = c3.neg(&mut cs.namespace(|| "c3 <- c3.neg()"))?;
        let c3 = x.c0.add(&mut cs.namespace(|| "c3 <- x.c0 + c3"), &c3)?;
        let c2 = x.c0.mul(&mut cs.namespace(|| "c2 <- x.c0 * x.c1"), &x.c1)?;
        let c0 = c0.mul(&mut cs.namespace(|| "c0 <- c0 * c3"), &c3)?;
        let c0 = c0.add(&mut cs.namespace(|| "c0 <- c0 + c2"), &c2)?;
        let z1 = c2.double(&mut cs.namespace(|| "z1 <- c2.double()"))?;
        let c2 = c2.mul_by_nonresidue(&mut cs.namespace(|| "c2 <- c2.mul_by_nonresidue()"))?;
        let z0 = c0.add(&mut cs.namespace(|| "z0 <- c0 + c2"), &c2)?;

        Ok(Self { c0: z0, c1: z1 })
    }

    pub fn inverse<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let val = BlsFp12::try_from(self).ok();
        let inv = val.and_then(|val| {
            if val.is_zero().into() {
                eprintln!("Inverse of zero Fp12 element cannot be calculated");
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

        let x = BlsFp12::try_from(self).ok();
        let y = BlsFp12::try_from(value).ok();
        let div = x.and_then(|x| {
            y.and_then(|y| {
                if y.is_zero().into() {
                    eprintln!("Division by zero Fp12 element cannot be calculated");
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
        let c0 = Fp6Element::<F>::conditionally_select(
            &mut cs.namespace(|| "cond c0"),
            &z0.c0,
            &z1.c0,
            condition,
        )?;
        let c1 = Fp6Element::<F>::conditionally_select(
            &mut cs.namespace(|| "cond c1"),
            &z0.c1,
            &z1.c1,
            condition,
        )?;
        Ok(Self { c0, c1 })
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
        let a = BlsFp12::random(&mut rng);
        let b = BlsFp12::random(&mut rng);
        let c = a + b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a+b"), &b_alloc).unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a+b = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["3000"]);
        expect_eq(cs.num_constraints(), &expect!["2796"]);
    }

    #[test]
    fn test_random_sub() {
        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let b = BlsFp12::random(&mut rng);
        let c = a - b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-b"), &b_alloc).unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a-b = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["3000"]);
        expect_eq(cs.num_constraints(), &expect!["2796"]);
    }

    #[test]
    fn test_random_mul() {
        use std::ops::Mul;

        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let b = BlsFp12::random(&mut rng);
        let c = a.mul(b);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.mul(&mut cs.namespace(|| "a*b"), &b_alloc).unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["10659"]);
        expect_eq(cs.num_constraints(), &expect!["10479"]);
    }

    #[test]
    fn test_random_square() {
        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let c = a.square();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.square(&mut cs.namespace(|| "a²")).unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a² = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["10466"]);
        expect_eq(cs.num_constraints(), &expect!["10370"]);
    }

    #[test]
    fn test_random_div() {
        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let mut b = BlsFp12::random(&mut rng);
        while b.invert().is_none().into() {
            b = BlsFp12::random(&mut rng);
        }
        let c = a * b.invert().unwrap();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .div_unchecked(&mut cs.namespace(|| "a div b"), &b_alloc)
            .unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a div b = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["13491"]);
        expect_eq(cs.num_constraints(), &expect!["13275"]);
    }

    #[test]
    fn test_random_mul_by_014() {
        use bls12_381::fp2::Fp2 as BlsFp2;

        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let c0 = BlsFp2::random(&mut rng);
        let c1 = BlsFp2::random(&mut rng);
        let b = BlsFp12 {
            c0: BlsFp6 {
                c0,
                c1,
                c2: BlsFp2::zero(),
            },
            c1: BlsFp6 {
                c0: BlsFp2::zero(),
                c1: BlsFp2::one(),
                c2: BlsFp2::zero(),
            },
        };
        let c = a * b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c0_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c0"), &Some(c0)).unwrap();
        let c1_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c1"), &Some(c1)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .mul_by_014(
                &mut cs.namespace(|| "a*(c0, c1)(014)"),
                &c0_alloc,
                &c1_alloc,
            )
            .unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["10156"]);
        expect_eq(cs.num_constraints(), &expect!["10032"]);
    }

    #[test]
    fn test_random_mul_014_by_014() {
        use bls12_381::fp2::Fp2 as BlsFp2;

        let mut rng = rand::thread_rng();
        let c0 = BlsFp2::random(&mut rng);
        let c1 = BlsFp2::random(&mut rng);
        let d0 = BlsFp2::random(&mut rng);
        let d1 = BlsFp2::random(&mut rng);
        let a = BlsFp12 {
            c0: BlsFp6 {
                c0,
                c1,
                c2: BlsFp2::zero(),
            },
            c1: BlsFp6 {
                c0: BlsFp2::zero(),
                c1: BlsFp2::one(),
                c2: BlsFp2::zero(),
            },
        };
        let b = BlsFp12 {
            c0: BlsFp6 {
                c0: d0,
                c1: d1,
                c2: BlsFp2::zero(),
            },
            c1: BlsFp6 {
                c0: BlsFp2::zero(),
                c1: BlsFp2::one(),
                c2: BlsFp2::zero(),
            },
        };
        let c = a * b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let c0_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c0"), &Some(c0)).unwrap();
        let c1_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c1"), &Some(c1)).unwrap();
        let d0_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc d0"), &Some(d0)).unwrap();
        let d1_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc d1"), &Some(d1)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = Fp12Element::mul_014_by_014(
            &mut cs.namespace(|| "(c0, c1)(014)*(d0, d1)(014)"),
            &c0_alloc,
            &c1_alloc,
            &d0_alloc,
            &d1_alloc,
        )
        .unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["8573"]);
        expect_eq(cs.num_constraints(), &expect!["8501"]);
    }

    #[test]
    fn test_random_mul_by_01245() {
        use bls12_381::fp2::Fp2 as BlsFp2;

        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let c00 = BlsFp2::random(&mut rng);
        let c01 = BlsFp2::random(&mut rng);
        let c02 = BlsFp2::random(&mut rng);
        let c11 = BlsFp2::random(&mut rng);
        let c12 = BlsFp2::random(&mut rng);
        let b = BlsFp12 {
            c0: BlsFp6 {
                c0: c00,
                c1: c01,
                c2: c02,
            },
            c1: BlsFp6 {
                c0: BlsFp2::zero(),
                c1: c11,
                c2: c12,
            },
        };
        let c = a * b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c00_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c00"), &Some(c00)).unwrap();
        let c01_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c01"), &Some(c01)).unwrap();
        let c02_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c02"), &Some(c02)).unwrap();
        let c11_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c11"), &Some(c11)).unwrap();
        let c12_alloc =
            Fp2Element::alloc_element(&mut cs.namespace(|| "alloc c12"), &Some(c12)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .mul_by_01245(
                &mut cs.namespace(|| "a*(c00, c01, c01, c11, c12)(01245)"),
                &c00_alloc,
                &c01_alloc,
                &c02_alloc,
                &c11_alloc,
                &c12_alloc,
            )
            .unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["10596"]);
        expect_eq(cs.num_constraints(), &expect!["10430"]);
    }

    #[test]
    fn test_random_conjugate() {
        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let c = a.conjugate();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .conjugate(&mut cs.namespace(|| "a.conjugate()"))
            .unwrap();
        Fp12Element::assert_is_equal(
            &mut cs.namespace(|| "a.conjugate() = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["2916"]);
        expect_eq(cs.num_constraints(), &expect!["2796"]);
    }

    #[test]
    fn test_random_inverse() {
        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let c = a.invert().unwrap();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.inverse(&mut cs.namespace(|| "a^-1")).unwrap();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a^-1 = c"), &res_alloc, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["13407"]);
        expect_eq(cs.num_constraints(), &expect!["13275"]);
    }

    #[test]
    fn test_random_alloc_is_zero() {
        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let b = BlsFp12::random(&mut rng);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-a"), &a_alloc).unwrap();
        let zero = Fp12Element::zero();
        Fp12Element::assert_is_equal(&mut cs.namespace(|| "a-a = 0"), &res_alloc, &zero).unwrap();
        let zbit_alloc = res_alloc
            .alloc_is_zero(&mut cs.namespace(|| "z <- a-a ?= 0"))
            .unwrap();
        let cond_alloc = Fp12Element::conditionally_select(
            &mut cs.namespace(|| "select(a, b, z)"),
            &a_alloc,
            &b_alloc,
            &Boolean::Is(zbit_alloc),
        )
        .unwrap();
        Fp12Element::assert_is_equal(
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
        expect_eq(cs.scalar_aux().len(), &expect!["13319"]);
        expect_eq(cs.num_constraints(), &expect!["13379"]);
    }
}
