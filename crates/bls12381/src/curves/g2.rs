use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::G2Affine;
use ff::{PrimeField, PrimeFieldBits};

use crate::fields::e2::AllocatedE2Element;

#[derive(Clone)]
pub struct AllocatedG2Point<F: PrimeField + PrimeFieldBits> {
    x: AllocatedE2Element<F>,
    y: AllocatedE2Element<F>,
}

impl<F> From<&G2Affine> for AllocatedG2Point<F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &G2Affine) -> Self {
        todo!()
    }
}

impl<F> From<&AllocatedG2Point<F>> for G2Affine
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &AllocatedG2Point<F>) -> Self {
        todo!()
    }
}

impl<F: PrimeField + PrimeFieldBits> AllocatedG2Point<F> {}
