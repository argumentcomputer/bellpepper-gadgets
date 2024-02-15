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
        BigInt::from(value).rem(p)
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

    // TODO: add tests
    // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-11#section-4.1
    // return in % 2
    // This requires `in` to be the unique element < p.
    // NOTE: different from Wahby-Boneh paper https://eprint.iacr.org/2019/403.pdf and python reference code: https://github.com/algorand/bls_sigs_ref/blob/master/python-impl/opt_swu_g2.py
    pub(crate) fn sgn0<CS>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // TODO: cleanup
        self.0
            .enforce_width_conditional(&mut cs.namespace(|| "ensure bitwidths in input"))?;

        // enforce that least significant limb is divisible by 2
        let out = match &self.0.limbs {
            EmulatedLimbs::Allocated(limbs) => {
                let least_sig = &limbs[0];
                let val = least_sig.get_value().unwrap();
                let val = BigInt::from_bytes_le(Sign::Plus, val.to_repr().as_ref());
                let out = &val % 2u64;
                let div = &val / 2u64;
                assert_eq!(2u64 * &div + &out, val.clone(), "sanity check");
                let out = if &out == &BigInt::from(0u64) {
                    false
                } else if &out == &BigInt::from(1u64) {
                    true
                } else {
                    panic!()
                };

                let out_bit =
                    AllocatedBit::alloc(&mut cs.namespace(|| "alloc sgn0 out"), Some(out))?;
                let div = AllocatedNum::alloc(&mut cs.namespace(|| "alloc sgn0 div"), || {
                    Ok(bigint_to_scalar(&div))
                })?;

                let two = F::ONE + F::ONE;
                cs.enforce(
                    || format!("enforce sgn0 bit"),
                    |lc| lc + CS::one(),
                    |lc| lc + (two, div.get_variable()) + out_bit.get_variable(), // 2 * div + out
                    |lc| lc + &least_sig.lc(F::ONE),                              // least_sig
                );
                out_bit
            }
            _ => {
                panic!("not implemented") // FIXME
            }
        };

        Ok(Boolean::from(out))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bls12_381::hash_to_curve::Sgn0;
    use pasta_curves::Fp;
    // use halo2curves::bn256::Fq as Fp;

    use expect_test::{expect, Expect};
    fn expect_eq(computed: usize, expected: &Expect) {
        expected.assert_eq(&computed.to_string());
    }

    fn big_to_circ(v: BlsFp) -> Vec<String> {
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
        res.into_iter().map(|b| format!("{}", b)).collect()
    }

    fn blsfp_to_bigint(value: BlsFp) -> BigInt {
        let bytes = value.to_bytes();
        assert!(bytes.len() == 48);
        BigInt::from_bytes_be(Sign::Plus, &bytes)
    }

    // #[test]
    // fn test_asdf() {
    //     let mut rng = rand::thread_rng();
    //     let a = BlsFp::random(&mut rng);
    //     let b = BlsFp::random(&mut rng);
    //     let c = a * b;
    //     eprintln!("a:{:?}", a);
    //     eprintln!("b:{:?}", b);
    //     eprintln!("c:{:?}", c);
    //     let a = big_to_circ(a);
    //     let b = big_to_circ(b);
    //     let c = big_to_circ(c);
    //     eprintln!("\"a\":{:?},", a);
    //     eprintln!("\"b\":{:?},", b);
    //     eprintln!("\"out\":{:?}", c);
    //     assert!(false);
    // }

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
        let mut c = a * b;
        // for _ in 0..99 {
        //     c *= b;
        // }

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let c_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc c"), &c).unwrap();
        let mut res_alloc = a_alloc.mul(&mut cs.namespace(|| "a*b"), &b_alloc).unwrap();
        // for i in 0..99 {
        //     res_alloc = res_alloc
        //         .mul(&mut cs.namespace(|| format!("mul {i}")), &b_alloc)
        //         .unwrap();
        // }
        FpElement::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc, &c_alloc).unwrap();
        // let r = BlsFp::from(&res_alloc);
        // eprintln!("c: {:?}\nr: {:?}", c, r);
        // eprintln!("c overflow: {}", c_alloc.0.overflow);
        // eprintln!("r overflow: {}", res_alloc.0.overflow);
        // let mut buf = String::new();
        // for mut l in cs.pretty_print_list().into_iter() {
        //     if l.starts_with("AUX") || l.starts_with("INPUT") {
        //         continue;
        //     }
        //     let l = l.replace("/", ";");
        //     //l.retain(|c| !c.is_digit(10));
        //     // let l = l
        //     //     .split("/")
        //     //     .collect::<Vec<_>>()
        //     //     .into_iter()
        //     //     .rev()
        //     //     .collect::<Vec<_>>()
        //     //     .join(";");
        //     let l = l + " 1";
        //     buf += &l;
        //     buf += "\n";
        // }
        // std::fs::write("/home/w/out.folded", &buf).unwrap();
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
    fn test_random_alloc_is_zero() {
        let mut rng = rand::thread_rng();
        let a = BlsFp::random(&mut rng);
        let b = BlsFp::random(&mut rng);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc a"), &a).unwrap();
        let b_alloc = FpElement::alloc_element(&mut cs.namespace(|| "alloc b"), &b).unwrap();
        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-a"), &a_alloc).unwrap();
        let z_alloc =
            FpElement::alloc_element(&mut cs.namespace(|| "alloc zero"), &BlsFp::zero()).unwrap();
        FpElement::assert_is_equal(&mut cs.namespace(|| "a-a = 0"), &res_alloc, &z_alloc).unwrap();
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
        expect_eq(cs.scalar_aux().len(), &expect!["1199"]);
        expect_eq(cs.num_constraints(), &expect!["1196"]);
    }
}
