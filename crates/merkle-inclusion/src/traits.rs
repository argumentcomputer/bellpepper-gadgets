use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_keccak::{keccak256, sha3};
use ff::PrimeField;

pub trait GadgetDigest<E: PrimeField> {
    /// Output size for our hasher, in bits.
    const OUTPUT_SIZE: usize;

    /// Get output size of the hasher.
    fn output_size() -> usize {
        Self::OUTPUT_SIZE
    }

    /// Compute hash of `input`.
    fn digest<CS: ConstraintSystem<E>>(
        cs: CS,
        input: &[Boolean],
    ) -> Result<Vec<Boolean>, SynthesisError>;
}

pub struct Sha3 {}

impl<E: PrimeField> GadgetDigest<E> for Sha3 {
    const OUTPUT_SIZE: usize = 256;

    fn digest<CS: ConstraintSystem<E>>(
        cs: CS,
        input: &[Boolean],
    ) -> Result<Vec<Boolean>, SynthesisError> {
        sha3(cs, input)
    }
}

pub struct Keccak {}

impl<E: PrimeField> GadgetDigest<E> for Keccak {
    const OUTPUT_SIZE: usize = 256;

    fn digest<CS: ConstraintSystem<E>>(
        cs: CS,
        input: &[Boolean],
    ) -> Result<Vec<Boolean>, SynthesisError> {
        keccak256(cs, input)
    }
}
