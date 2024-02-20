use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use bellpepper_emulated::{
    field_element::{
        EmulatedFieldElement, EmulatedFieldParams, EmulatedLimbs, PseudoMersennePrime,
    },
    util::bigint_to_scalar,
};
use bls12_381::fp::Fp as BlsFp;
use ff::PrimeFieldBits;
use num_bigint::{BigInt, Sign};

pub struct Bls12381FpParams;

impl EmulatedFieldParams for Bls12381FpParams {
    // TODO: Depending on the native field, different limb/bit pairs are more optimal and have less waste. This should be customizable and not hardcoded
    // for example, in the pasta field, 4/96 could be used instead
    fn num_limbs() -> usize {
        6
        //4
    }

    fn bits_per_limb() -> usize {
        64
        //96
    }

    fn modulus() -> BigInt {
        BigInt::parse_bytes(
            b"1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab",
            16,
        )
        .unwrap()
    }

    fn is_modulus_pseudo_mersenne() -> bool {
        false
    }

    fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
        None
    }
}

impl Bls12381FpParams {
    /// Third root of unity
    pub fn w<F: PrimeFieldBits>() -> FpElement<F> {
        FpElement::<F>::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()
    }
}

pub type Bls12381Fp<F> = EmulatedFieldElement<F, Bls12381FpParams>;

#[derive(Clone)]
pub struct FpElement<F: PrimeFieldBits>(pub(crate) Bls12381Fp<F>);

pub struct Bls12381FrParams;

impl EmulatedFieldParams for Bls12381FrParams {
    fn num_limbs() -> usize {
        4
    }

    fn bits_per_limb() -> usize {
        64
    }

    fn modulus() -> BigInt {
        BigInt::parse_bytes(
            b"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
            16,
        )
        .unwrap()
    }

    fn is_modulus_pseudo_mersenne() -> bool {
        false
    }

    fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
        None
    }
}

pub type Bls12381Fr<F> = EmulatedFieldElement<F, Bls12381FrParams>;

impl<F> From<&BlsFp> for FpElement<F>
where
    F: PrimeFieldBits,
{
    fn from(value: &BlsFp) -> Self {
        let bytes = value.to_bytes();
        assert!(bytes.len() == 48);
        let val = BigInt::from_bytes_be(Sign::Plus, &bytes);
        Self(Bls12381Fp::<F>::from(&val))
    }
}

pub(crate) fn bigint_to_fpelem(val: &BigInt) -> Option<BlsFp> {
    use num_traits::Zero;
    if val >= &Bls12381FpParams::modulus() {
        return None;
    }
    let be_bytes = BigInt::to_bytes_be(val);
    if be_bytes.0 != Sign::Plus {
        // the sign is only non-positive if the value is exactly 0
        assert!(val == &BigInt::zero());
    }
    let mut bytes: Vec<u8> = be_bytes.1;
    assert!(bytes.len() <= 48);
    bytes.splice(0..0, vec![0; 48 - bytes.len()]);
    let bytes: [u8; 48] = bytes.try_into().unwrap();
    Some(BlsFp::from_bytes(&bytes).unwrap())
}

pub(crate) fn emulated_to_native<F>(value: &Bls12381Fp<F>) -> BlsFp
where
    F: PrimeFieldBits,
{
    use std::ops::Rem;
    let p = &Bls12381FpParams::modulus();
    let val = BigInt::from(value).rem(p);
    bigint_to_fpelem(&val).unwrap()
}

impl<F> From<&FpElement<F>> for BlsFp
where
    F: PrimeFieldBits,
{
    fn from(value: &FpElement<F>) -> Self {
        emulated_to_native(&value.0)
    }
}

impl<F: PrimeFieldBits> From<&FpElement<F>> for BigInt {
    fn from(value: &FpElement<F>) -> Self {
        use std::ops::Rem;
        let p = &Bls12381FpParams::modulus();
        Self::from(&value.0).rem(p)
    }
}

impl<F: PrimeFieldBits> FpElement<F> {
    pub fn from_dec(val: &str) -> Option<Self> {
        BigInt::parse_bytes(val.as_bytes(), 10)
            .as_ref()
            .and_then(bigint_to_fpelem)
            .as_ref()
            .map(Self::from)
    }

    pub fn zero() -> Self {
        Self(Bls12381Fp::zero())
    }

    pub fn one() -> Self {
        Self(Bls12381Fp::one())
    }

    pub fn alloc_element<CS>(cs: &mut CS, value: &BlsFp) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let val_alloc = Self::from(value);
        let alloc = val_alloc
            .0
            .allocate_field_element_unchecked(&mut cs.namespace(|| "alloc fp elm"))?;

        Ok(Self(alloc))
    }

    pub fn assert_is_equal<CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Bls12381Fp::<F>::assert_is_equal(&mut cs.namespace(|| "a = b"), &a.0, &b.0)?;
        Ok(())
    }

    pub fn reduce<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let val_reduced = self.0.reduce(&mut cs.namespace(|| "val mod P"))?;
        Ok(Self(val_reduced))
    }

    pub fn assert_equality_to_constant<CS>(
        &self,
        cs: &mut CS,
        constant: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.0
            .assert_equality_to_constant(&mut cs.namespace(|| "val =? (const) val"), &constant.0)?;
        Ok(())
    }

    pub fn alloc_is_zero<CS>(&self, cs: &mut CS) -> Result<AllocatedBit, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.0.alloc_is_zero(&mut cs.namespace(|| "val =? 0"))
    }

    pub fn add<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self.0.add(&mut cs.namespace(|| "a + b"), &value.0)?;
        Ok(Self(res))
    }

    pub fn sub<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self.0.sub(&mut cs.namespace(|| "a - b"), &value.0)?;
        Ok(Self(res))
    }

    pub fn mul<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self.0.mul(&mut cs.namespace(|| "a * b"), &value.0)?;
        Ok(Self(res))
    }

    pub fn inverse<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self.0.inverse(&mut cs.namespace(|| "x.inverse()"))?;
        Ok(Self(res))
    }

    pub fn div_unchecked<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self.0.divide(&mut cs.namespace(|| "a div b"), &value.0)?;
        Ok(Self(res))
    }

    pub fn square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.mul(&mut cs.namespace(|| "x.square()"), self)
    }

    pub fn double<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.add(&mut cs.namespace(|| "x.double()"), self)
    }

    pub fn mul_const<CS>(&self, cs: &mut CS, value: &BigInt) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self
            .0
            .mul_const(&mut cs.namespace(|| "a * constval"), value)?;
        Ok(Self(res))
    }

    pub fn neg<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self.0.neg(&mut cs.namespace(|| "-a"))?;
        Ok(Self(res))
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
        let res = Bls12381Fp::<F>::conditionally_select(
            &mut cs.namespace(|| "cond val"),
            &z0.0,
            &z1.0,
            condition,
        )?;
        Ok(Self(res))
    }

    /// Implements [sgn0](https://datatracker.ietf.org/doc/html/rfc9380#name-the-sgn0-function) which returns `x mod 2`
    /// Enforces that self is reduced
    pub fn sgn0<CS>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.0
            .enforce_width_conditional(&mut cs.namespace(|| "ensure bitwidths in input"))?;

        let least_sig = match &self.0.limbs {
            EmulatedLimbs::Allocated(limbs) => limbs[0].get_value().unwrap(),
            EmulatedLimbs::Constant(limbs) => limbs[0],
        };

        let (out_val, div) = {
            let val = BigInt::from_bytes_le(Sign::Plus, least_sig.to_repr().as_ref());
            let out = &val % 2u64;
            let div = &val / 2u64;
            assert_eq!(2u64 * &div + &out, val.clone(), "sanity check");
            if out == BigInt::from(0u64) {
                (false, div)
            } else if out == BigInt::from(1u64) {
                (true, div)
            } else {
                unreachable!("Division by 2 always returns 0 or 1")
            }
        };

        let out = match &self.0.limbs {
            EmulatedLimbs::Allocated(limbs) => {
                let out_bit =
                    AllocatedBit::alloc(&mut cs.namespace(|| "alloc sgn0 out"), Some(out_val))?;
                let div = AllocatedNum::alloc(&mut cs.namespace(|| "alloc sgn0 div"), || {
                    Ok(bigint_to_scalar(&div))
                })?;

                // enforce that least significant limb is divisible by 2
                let two = F::ONE + F::ONE;
                cs.enforce(
                    || "enforce sgn0 bit",
                    |lc| lc + CS::one(),
                    |lc| lc + (two, div.get_variable()) + out_bit.get_variable(), // 2 * div + out
                    |lc| lc + &limbs[0].lc(F::ONE),                              // least_sig
                );
                Boolean::from(out_bit)
            }
            EmulatedLimbs::Constant(_) => {
                Boolean::Constant(out_val)
            }
        };

        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bls12_381::hash_to_curve::Sgn0;
    use pasta_curves::Fp;

    use expect_test::{expect, Expect};
    fn expect_eq(computed: usize, expected: &Expect) {
        expected.assert_eq(&computed.to_string());
    }

    #[test]
    fn test_random_add() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = a + b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a+b"), &b_alloc).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a+b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["277"]);
        expect_eq(cs.num_constraints(), &expect!["262"]);
    }

    #[test]
    fn test_random_sub() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = a - b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-b"), &b_alloc).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a-b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["277"]);
        expect_eq(cs.num_constraints(), &expect!["262"]);
    }

    #[test]
    fn test_random_mul() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = a * b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.mul(&mut cs.namespace(|| "a*b"), &b_alloc).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["681"]);
        expect_eq(cs.num_constraints(), &expect!["666"]);
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
    }

    #[test]
    fn test_random_mul_const() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        // the product can't overflow or mul_const fails, so use a very small value here
        let b = BlsFp::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x7f,
        ])
        .unwrap();
        let c = a * b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_elem: FpElement<Fp> = (&b).into();
        let b_val: BigInt = (&b_elem.0).into();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc
            .mul_const(&mut cs.namespace(|| "a*b (const)"), &b_val)
            .unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["271"]);
        expect_eq(cs.num_constraints(), &expect!["262"]);
    }

    #[test]
    fn test_random_neg() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let c = -&a;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let res_alloc = a_alloc.neg(&mut cs.namespace(|| "-a")).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "-a = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["271"]);
        expect_eq(cs.num_constraints(), &expect!["262"]);
    }

    #[test]
    fn test_random_sgn0() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let c: bool = a.sgn0().into();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let c_alloc = AllocatedBit::alloc(&mut cs.namespace(|| "alloc c"), Some(c)).unwrap();
        let res_alloc = a_alloc.sgn0(&mut cs.namespace(|| "a.sgn0()")).unwrap();
        Boolean::enforce_equal(
            &mut cs.namespace(|| "a.sgn0() = c"),
            &res_alloc,
            &Boolean::from(c_alloc),
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["9"]);
        expect_eq(cs.num_constraints(), &expect!["4"]);
    }

    #[test]
    fn test_sgn0() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let zero = FpElement::zero()
            .sgn0(&mut cs.namespace(|| "sgn0(0)"))
            .unwrap();
        assert!(matches!(zero, Boolean::Constant(false)));
        let one = FpElement::one()
            .sgn0(&mut cs.namespace(|| "sgn0(1)"))
            .unwrap();
        assert!(matches!(one, Boolean::Constant(true)));
        let neg_one = FpElement::one().neg(&mut cs.namespace(|| "-1")).unwrap();
        let neg_one = neg_one.sgn0(&mut cs.namespace(|| "sgn0(-1)")).unwrap();
        assert!(matches!(neg_one, Boolean::Constant(false)));
        let neg_zero = FpElement::zero().neg(&mut cs.namespace(|| "-0")).unwrap();
        let neg_zero = neg_zero.sgn0(&mut cs.namespace(|| "sgn0(-0)")).unwrap();
        assert!(matches!(neg_zero, Boolean::Constant(false)));

        // p-1 / 2
        let p_m1_over2 = FpElement(Bls12381Fp::<Fp>::from(
            &((Bls12381FpParams::modulus() - BigInt::from(1)) / BigInt::from(2)),
        ));
        let p_p1_over2 = p_m1_over2
            .add(&mut cs.namespace(|| "p-1_over2 + 1"), &FpElement::one())
            .unwrap();
        let neg_p_p1_over2 = p_p1_over2
            .neg(&mut cs.namespace(|| "-(p-1_over2+1)"))
            .unwrap();
        let p_m1_over2 = p_m1_over2
            .sgn0(&mut cs.namespace(|| "sgn0(p-1_over2)"))
            .unwrap();
        assert!(matches!(p_m1_over2, Boolean::Constant(true)));
        let p_p1_over2 = p_p1_over2
            .sgn0(&mut cs.namespace(|| "sgn0(p-1_over2+1)"))
            .unwrap();
        assert!(matches!(p_p1_over2, Boolean::Constant(false)));
        let neg_p_p1_over2 = neg_p_p1_over2
            .sgn0(&mut cs.namespace(|| "sgn0(-(p-1_over2+1))"))
            .unwrap();
        Boolean::enforce_equal(
            &mut cs.namespace(|| "-(p-1_over2+1) == p_m1_over2"),
            &neg_p_p1_over2,
            &p_m1_over2,
        )
        .unwrap();

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.scalar_aux().len(), 0);
        assert_eq!(cs.num_constraints(), 0);
    }

    #[test]
    fn test_random_alloc_is_zero() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-a"), &a_alloc).unwrap();
        let zero = FpElement::zero();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a-a = 0"), &res_alloc, &zero).unwrap();
        let zbit_alloc = res_alloc
            .alloc_is_zero(&mut cs.namespace(|| "z <- a-a ?= 0"))
            .unwrap();
        let cond_alloc = FpElement::conditionally_select(
            &mut cs.namespace(|| "select(a, b, z)"),
            &a_alloc,
            &b_alloc,
            &Boolean::Is(zbit_alloc),
        )
        .unwrap();
        FpElement::assert_is_equal(
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
        expect_eq(cs.scalar_aux().len(), &expect!["1193"]);
        expect_eq(cs.num_constraints(), &expect!["1196"]);
    }
}
