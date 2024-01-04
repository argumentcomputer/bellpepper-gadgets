use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::G1Affine;
use ff::{PrimeField, PrimeFieldBits};

use crate::fields::fp::AllocatedFieldElement;

#[derive(Clone)]
pub struct AllocatedG1Point<F: PrimeField + PrimeFieldBits> {
    x: AllocatedFieldElement<F>,
    y: AllocatedFieldElement<F>,
}

impl<F> From<&G1Affine> for AllocatedG1Point<F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &G1Affine) -> Self {
        todo!()
    }
}

impl<F> From<&AllocatedG1Point<F>> for G1Affine
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &AllocatedG1Point<F>) -> Self {
        todo!()
    }
}

impl<F: PrimeField + PrimeFieldBits> AllocatedG1Point<F> {}
