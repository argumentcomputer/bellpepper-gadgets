pub mod traits;

use crate::traits::GadgetDigest;
use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

// HashValue represents the digest type output from the hash function
pub type HashValue = Vec<Boolean>;
pub type Key = Vec<Boolean>;
const HASH_LENGTH: usize = 32 * 8;

/// Represents a leaf node in a Jellyfish Merkle Tree.
///
/// Each leaf node contains a key-value pair, where the key is used to determine the position in the tree and the value
/// is the data stored.
pub struct Leaf {
    key: Key,
    value_hash: HashValue,
}

impl Leaf {
    pub fn new(key: Key, value_hash: HashValue) -> Self {
        Self { key, value_hash }
    }
    pub fn hash(&self) -> &HashValue {
        &self.value_hash
    }

    pub fn key(&self) -> &HashValue {
        &self.key
    }
}

/// Contains a leaf node and sibling hashes required for proof verification in a Merkle Tree.
///
/// The `Proof` struct is essential for the Merkle Tree's cryptographic verification process, providing the necessary
/// information to verify the integrity and authenticity of the data.
pub struct Proof {
    leaf: Leaf,
    siblings: Vec<HashValue>,
}

impl Proof {
    pub fn new(leaf: Leaf, siblings: Vec<HashValue>) -> Self {
        Self { leaf, siblings }
    }

    pub fn leaf(&self) -> &Leaf {
        &self.leaf
    }

    pub fn siblings(&self) -> &[Vec<Boolean>] {
        &self.siblings
    }
}

/// Verifies the Merkle Tree proof against an expected root hash.
///
/// This function reconstructs the root hash from the given leaf and sibling hashes and compares it against the provided
/// expected root hash.
///
/// # Arguments
/// * `cs` - A mutable reference to the constraint system.
/// * `expected_root` - The expected root hash of the Merkle Tree.
/// * `proof` - The proof containing the leaf and its sibling hashes.
///
/// # Returns
/// A result containing the reconstructed root hash if successful, or a `SynthesisError` otherwise.
pub fn verify_proof<E, CS, GD>(
    mut cs: CS,
    expected_root: Vec<Boolean>,
    proof: Proof,
) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
    GD: GadgetDigest<E>,
{
    assert_eq!(expected_root.len(), GD::output_size());

    //Assert that we do not have more siblings than the length of our hash (otherwise cannot know which path to go)
    assert!(
        proof.siblings.len() <= HASH_LENGTH,
        "Merkle Tree proof has more than {} ({}) siblings.",
        HASH_LENGTH,
        proof.siblings.len(),
    );

    // Reconstruct the root hash from the leaf and sibling hashes
    let mut actual_root_hash = proof.leaf().hash().to_vec();

    for (i, (sibling_hash, bit)) in proof
        .siblings()
        .to_vec()
        .iter()
        .zip(
            proof
                .leaf()
                .key()
                .iter()
                .rev()
                .skip(GD::output_size() - proof.siblings().len()),
        )
        .enumerate()
    {
        if let Some(b) = bit.get_value() {
            if b {
                actual_root_hash = GD::digest(
                    cs.namespace(|| format!("sibling {}", i)),
                    &[sibling_hash.to_owned(), actual_root_hash].concat(),
                )?
            } else {
                actual_root_hash = GD::digest(
                    cs.namespace(|| format!("sibling {}", i)),
                    &[actual_root_hash, sibling_hash.to_owned()].concat(),
                )?
            }
        } else {
            return Err(SynthesisError::Unsatisfiable);
        }
    }

    hash_equality(cs, expected_root, actual_root_hash)
}

/// Compares two hash values for equality bit by bit.
///
/// # Arguments
/// * `cs` - A mutable reference to the constraint system.
/// * `expected` - The expected hash value.
/// * `actual` - The actual hash value to compare against.
///
/// # Returns
/// A result containing the actual hash value if the hashes are equal, or a `SynthesisError` otherwise.
fn hash_equality<E, CS>(
    mut cs: CS,
    expected: HashValue,
    actual: HashValue,
) -> Result<HashValue, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    if expected.len() != actual.len() {
        // TODO better error
        return Err(SynthesisError::Unsatisfiable);
    }

    // Check if the reconstructed root hash matches the expected root hash
    for i in 0..expected.len() - 1 {
        Boolean::enforce_equal(
            cs.namespace(|| format!("equality on {} hash bit", i)),
            &expected[i],
            &actual[i],
        )?;
    }
    Ok(actual)
}
