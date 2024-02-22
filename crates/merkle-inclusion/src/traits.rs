use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

/// A trait for implementing hash digest gadgets.
///
/// This trait defines the necessary methods for computing hash digests within constraint systems.
pub trait GadgetDigest<E: PrimeField> {
    /// Output size for our hasher, in bytes.
    const OUTPUT_SIZE: usize;

    /// Rust hasher to use out of circuit along with the GadgetDigest we are referring to. For testing purposes.
    type OutOfCircuitHasher: digest::Digest;

    /// Get output size of the hasher.
    fn output_size() -> usize {
        // Ensures that the output size is the same as the OutOfCircuitHasher digest output size.
        debug_assert_eq!(
            <Self::OutOfCircuitHasher as digest::Digest>::output_size(),
            Self::OUTPUT_SIZE,
            "GadgetDigest and OutOfCircuitHasher output size are non-equal"
        );
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
/// This macro generates an empty struct and implements the `GadgetDigest` trait for it, simplifying the process of
/// creating new hash digest gadgets.
///
/// # Parameters
/// * `struct_name` - The name of the struct to be generated.
/// * `digest_method` - The digest method to be used in the implementation.
/// * `output_size` - The output size of the hasher, in bytes.
/// * `out_of_circuit_hasher` - Rust hasher to use out of circuit along with the GadgetDigest we are referring to.
/// * `is_little_endian` - Boolean to tell us if the hashing algorithm is little or big endian.
#[macro_export]
macro_rules! create_gadget_digest_impl {
    ($struct_name:ident, $digest_method:path, $output_size:expr, $out_of_circuit_hasher:ty) => {
        pub struct $struct_name {}

        impl<E: PrimeField> GadgetDigest<E> for $struct_name {
            const OUTPUT_SIZE: usize = $output_size;
            type OutOfCircuitHasher = $out_of_circuit_hasher;

            fn digest<CS: ConstraintSystem<E>>(
                mut cs: CS,
                input: &[Boolean],
            ) -> Result<Vec<Boolean>, SynthesisError> {
                $digest_method(&mut cs.namespace(|| "digest data"), input)
            }
        }
    };
}
