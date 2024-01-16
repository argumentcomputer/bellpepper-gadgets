use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, SynthesisError,
};
use bellpepper_emulated::field_element::{
    EmulatedFieldElement, EmulatedFieldParams, PseudoMersennePrime,
};
use bls12_381::fp::Fp as BlsFp;
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::{BigInt, Sign};

#[derive(Debug)]
pub struct Bls12381FpParams;

impl EmulatedFieldParams for Bls12381FpParams {
    // TODO: Depending on the native field, different limb/bit pairs are more optimal and have less waste. This should be customizable and not hardcoded
    // for example, in the pasta field, 4/96 could be used instead
    fn num_limbs() -> usize {
        6
    }

    fn bits_per_limb() -> usize {
        64
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

pub type Bls12381Fp<F> = EmulatedFieldElement<F, Bls12381FpParams>;

#[derive(Clone)]
pub struct AllocatedFieldElement<F: PrimeField + PrimeFieldBits>(pub(crate) Bls12381Fp<F>);

#[derive(Debug)]
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

impl<F> From<&BlsFp> for AllocatedFieldElement<F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &BlsFp) -> Self {
        let bytes = value.to_bytes();
        assert!(bytes.len() == 48);
        let val = BigInt::from_bytes_be(Sign::Plus, &bytes);
        Self(Bls12381Fp::<F>::from(&val))
    }
}

/// FIXME: gross function, CLEANUP
pub fn bigint_to_fpelem(val: &BigInt) -> Option<BlsFp> {
    use num_traits::Zero;
    if val >= &Bls12381FpParams::modulus() {
        return None;
    }
    let res = BigInt::to_bytes_be(val);
    // eprintln!("{:#?}", res);
    // eprintln!("{:#?}", res.1.len());
    if res.0 != Sign::Plus {
        assert!(val == &BigInt::zero());
    }
    let mut bytes: Vec<u8> = res.1;
    assert!(bytes.len() <= 48);
    while bytes.len() < 48 {
        bytes.insert(0, 0);
    }
    let bytes: [u8; 48] = bytes.try_into().unwrap();
    Some(BlsFp::from_bytes(&bytes).unwrap())
}

pub fn emulated_to_native<F>(value: &Bls12381Fp<F>) -> BlsFp
where
    F: PrimeField + PrimeFieldBits,
{
    use std::ops::Rem;
    let p = &Bls12381FpParams::modulus();
    let val = BigInt::from(value).rem(p);
    bigint_to_fpelem(&val).unwrap()
}

impl<F> From<&AllocatedFieldElement<F>> for BlsFp
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &AllocatedFieldElement<F>) -> Self {
        emulated_to_native(&value.0)
    }
}

impl<F: PrimeField + PrimeFieldBits> AllocatedFieldElement<F> {
    pub fn from_dec(val: &str) -> Result<Self, SynthesisError> {
        let bigint = BigInt::parse_bytes(val.as_bytes(), 10).unwrap(); // FIXME: no unwraps
        let elm = bigint_to_fpelem(&bigint).unwrap();
        Ok(Self::from(&elm))
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
        let val_alloc = AllocatedFieldElement::<F>::from(value);
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
        let res = self
            .0
            .add(&mut cs.namespace(|| "compute a add b"), &value.0)?;
        Ok(Self(res))
    }

    pub fn sub<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self
            .0
            .sub(&mut cs.namespace(|| "compute a sub b"), &value.0)?;
        Ok(Self(res))
    }

    pub fn mul<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self
            .0
            .mul(&mut cs.namespace(|| "compute a mul b"), &value.0)?;
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
        let res = self
            .0
            .divide(&mut cs.namespace(|| "compute a div b"), &value.0)?;
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
            .mul_const(&mut cs.namespace(|| "compute a * constval"), value)?;
        Ok(Self(res))
    }

    pub fn neg<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let res = self.0.neg(&mut cs.namespace(|| "compute -a"))?;
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use pasta_curves::Fp;

    #[test]
    fn test_random_add() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = &a + &b;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let c_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a+b"), &b_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedFieldElement::assert_is_equal(
            &mut cs.namespace(|| "a+b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 262);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_sub() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = &a - &b;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let c_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-b"), &b_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedFieldElement::assert_is_equal(
            &mut cs.namespace(|| "a-b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 262);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_mul() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = &a * &b;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let c_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.mul(&mut cs.namespace(|| "a*b"), &b_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedFieldElement::assert_is_equal(
            &mut cs.namespace(|| "a*b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 666);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_mul_const() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        // the product can't overflow so use a small constant -- FIXME: could theoretically fail if the random is unlucky enough?
        let b = BlsFp::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x7f,
        ])
        .unwrap();
        let c = &a * &b.into();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_elem: AllocatedFieldElement<Fp> = (&b).into();
        let b_val: BigInt = (&b_elem.0).into();

        let c_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.mul_const(&mut cs.namespace(|| "a*b (const)"), &b_val);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedFieldElement::assert_is_equal(
            &mut cs.namespace(|| "a*b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 262);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_neg() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let c = -&a;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let c_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.neg(&mut cs.namespace(|| "-a"));
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedFieldElement::assert_is_equal(
            &mut cs.namespace(|| "-a = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 262);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_alloc_is_zero() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = b.clone();
        let zero = BlsFp::zero();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let a2_alloc =
            AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc a2"), &a.neg());
        assert!(a2_alloc.is_ok());
        let a2_alloc = a2_alloc.unwrap();

        let b_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a-a"), &a2_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let c_alloc = AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let z_alloc =
            AllocatedFieldElement::alloc_element(&mut cs.namespace(|| "alloc zero"), &zero);
        assert!(z_alloc.is_ok());
        let z_alloc = z_alloc.unwrap();

        let eq_alloc = AllocatedFieldElement::assert_is_equal(
            &mut cs.namespace(|| "a-a = 0"),
            &res_alloc,
            &z_alloc,
        );
        assert!(eq_alloc.is_ok());

        let zbit_alloc = res_alloc.alloc_is_zero(&mut cs.namespace(|| "z <- a-a ?= 0"));
        assert!(zbit_alloc.is_ok());
        let zbit_alloc = zbit_alloc.unwrap();

        let cond_alloc = AllocatedFieldElement::conditionally_select(
            &mut cs.namespace(|| "select(a, b, z)"),
            &a_alloc,
            &b_alloc,
            &Boolean::Is(zbit_alloc),
        );
        assert!(cond_alloc.is_ok());
        let cond_alloc = cond_alloc.unwrap();

        let eq_alloc = AllocatedFieldElement::assert_is_equal(
            &mut cs.namespace(|| "select(a, b, z) = c = b"),
            &cond_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1196);
        assert_eq!(cs.num_inputs(), 1);
    }
}
