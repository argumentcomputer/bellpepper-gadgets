use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, SynthesisError,
};
use bellpepper_emulated::field_element::{
    EmulatedFieldElement, EmulatedFieldParams, PseudoMersennePrime,
};
use bls12_381::fp::Fp as BlsFp;
use ff::PrimeFieldBits;
use num_bigint::{BigInt, Sign};

pub struct Bls12381FpParams;

impl EmulatedFieldParams for Bls12381FpParams {
    // TODO: Depending on the native field, different limb/bit pairs are more optimal and have less waste. This should be customizable and not hardcoded
    // for example, in the pasta field, 4/96 could be used instead for savings, but in bn256 7/55 is better
    fn num_limbs() -> usize {
        7
    }

    fn bits_per_limb() -> usize {
        55
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

pub(crate) fn emulated_to_native<F>(value: &Bls12381Fp<F>) -> Option<BlsFp>
where
    F: PrimeFieldBits,
{
    use std::ops::Rem;
    let p = &Bls12381FpParams::modulus();
    let val = BigInt::try_from(value).ok().map(|v| v.rem(p));
    val.and_then(|v| bigint_to_fpelem(&v))
}

pub(crate) fn big_from_dec(v: &str) -> Option<BigInt> {
    BigInt::parse_bytes(v.as_bytes(), 10)
}

pub(crate) fn fp_from_dec(v: &str) -> Option<BlsFp> {
    big_from_dec(v).as_ref().and_then(bigint_to_fpelem)
}

impl<F> TryFrom<&FpElement<F>> for BlsFp
where
    F: PrimeFieldBits,
{
    type Error = SynthesisError;

    fn try_from(value: &FpElement<F>) -> Result<Self, Self::Error> {
        emulated_to_native(&value.0).ok_or(SynthesisError::AssignmentMissing)
    }
}

impl<F: PrimeFieldBits> TryFrom<&FpElement<F>> for BigInt {
    type Error = SynthesisError;

    fn try_from(value: &FpElement<F>) -> Result<Self, Self::Error> {
        use std::ops::Rem;
        let p = &Bls12381FpParams::modulus();
        Self::try_from(&value.0).map(|v| v.rem(p))
    }
}

impl<F: PrimeFieldBits> FpElement<F> {
    pub fn from_dec(val: &str) -> Option<Self> {
        fp_from_dec(val).as_ref().map(Self::from)
    }

    pub fn zero() -> Self {
        Self(Bls12381Fp::zero())
    }

    pub fn one() -> Self {
        Self(Bls12381Fp::one())
    }

    pub fn alloc_element<CS>(cs: &mut CS, value: &Option<BlsFp>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let val: Option<BigInt> = value.and_then(|v| BigInt::try_from(&Self::from(&v)).ok());
        let alloc = Bls12381Fp::<F>::allocate_optional_field_element_unchecked(
            &mut cs.namespace(|| "alloc fp elm"),
            &val,
        )?;

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

    pub fn sgn0<CS>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.0.sgn0(cs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bls12_381::hash_to_curve::Sgn0;
    use halo2curves::bn256::Fq as Fp;

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
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a+b"), &b_alloc).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a+b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["250"]);
        expect_eq(cs.num_constraints(), &expect!["233"]);
    }

    #[test]
    fn test_random_sub() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = a - b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-b"), &b_alloc).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a-b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["250"]);
        expect_eq(cs.num_constraints(), &expect!["233"]);
    }

    #[test]
    fn test_random_mul() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = a * b;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.mul(&mut cs.namespace(|| "a*b"), &b_alloc).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["784"]);
        expect_eq(cs.num_constraints(), &expect!["769"]);
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
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_elem: FpElement<Fp> = (&b).into();
        let b_val: BigInt = (&b_elem.0).try_into().unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc
            .mul_const(&mut cs.namespace(|| "a*b (const)"), &b_val)
            .unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["243"]);
        expect_eq(cs.num_constraints(), &expect!["233"]);
    }

    #[test]
    fn test_random_neg() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let c = -&a;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = a_alloc.neg(&mut cs.namespace(|| "-a")).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "-a = c"), &res_alloc, &c_alloc).unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["243"]);
        expect_eq(cs.num_constraints(), &expect!["233"]);
    }

    #[test]
    fn test_random_sgn0() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let c: bool = a.sgn0().into();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
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
        expect_eq(cs.scalar_aux().len(), &expect!["10"]);
        expect_eq(cs.num_constraints(), &expect!["4"]);
    }

    #[test]
    fn test_random_alloc_is_zero() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
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
        expect_eq(cs.scalar_aux().len(), &expect!["1109"]);
        expect_eq(cs.num_constraints(), &expect!["1114"]);
    }
}
