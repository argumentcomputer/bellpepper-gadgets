use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_keccak::{keccak256, sha3};
use ff::PrimeField;

/// A trait for implementing hash digest gadgets.
///
/// This trait defines the necessary methods for computing hash digests within constraint systems.
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

/// A macro for creating implementations of the `GadgetDigest` trait.
///
/// This macro generates an empty struct and implements the `GadgetDigest` trait for it,
/// simplifying the process of creating new hash digest gadgets.
///
/// # Parameters
/// * `struct_name` - The name of the struct to be generated.
/// * `digest_method` - The digest method to be used in the implementation.
/// * `output_size` - The output size of the hasher, in bits.
macro_rules! create_gadget_digest_impl {
    ($struct_name:ident, $digest_method:path, $output_size:expr) => {
        pub struct $struct_name {}

        impl<E: PrimeField> GadgetDigest<E> for $struct_name {
            const OUTPUT_SIZE: usize = $output_size;

            fn digest<CS: ConstraintSystem<E>>(
                cs: CS,
                input: &[Boolean],
            ) -> Result<Vec<Boolean>, SynthesisError> {
                $digest_method(cs, input)
            }
        }
    };
}

create_gadget_digest_impl!(Sha3, sha3, 256);
create_gadget_digest_impl!(Keccak, keccak256, 256);
