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
use num_traits::{FromPrimitive, Zero};

pub trait EmulatedPairing<F, G1Element, G2Element, GtElement>
where
    F: PrimeField + PrimeFieldBits,
{
    fn miller_loop<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: [&G1Element],
        g2: [&G2Element],
    ) -> Result<GtElement, SynthesisError>;

    fn final_exponentiation<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        gt: &GtElement,
    ) -> Result<GtElement, SynthesisError>;

    fn pair<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: [&G1Element],
        g2: [&G2Element],
    ) -> Result<GtElement, SynthesisError>;

    fn assert_pairing_check<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g1: [&G1Element],
        g2: [&G2Element],
    ) -> Result<(), SynthesisError>;
}
