pub mod traits;

use crate::traits::GadgetDigest;
use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

// HashValue represents the digest type output from the hash function
pub type HashValue = Vec<Boolean>;
pub type Key = Vec<Boolean>;

/// Represents a leaf node in a Jellyfish Merkle Tree.
///
/// Each leaf node contains a key-value pair, where the key is used to determine the position in the tree and the value
/// is the data stored.
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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
/// # Notes
///
/// To reconstruct the root from the proof, the method iterate over the provided proof.leaf.key and the proof.siblings
/// in the same order. The order is from the bottom of the tree to its root, so from the first sibling to the last.
///
/// # Returns
/// A result containing the reconstructed root hash if successful, or a `SynthesisError` otherwise.
pub fn verify_proof<E, CS, GD>(
    mut cs: CS,
    expected_root: &[Boolean],
    proof: &Proof,
) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
    GD: GadgetDigest<E>,
{
    assert_eq!(expected_root.len(), GD::output_size() * 8);

    assert!(
        proof.siblings.len() <= proof.leaf().key().len(),
        "Merkle Tree proof has more siblings ({}) than the key length ({}).",
        proof.siblings().len(),
        proof.leaf().key().len(),
    );

    let mut actual_root_hash = proof.leaf().hash().to_vec();

    for (i, (bit, sibling_hash)) in proof
        .leaf()
        .key()
        .iter()
        .take(proof.siblings().len())
        .zip(proof.siblings().iter())
        .enumerate()
    {
        let b = bit.get_value().ok_or(SynthesisError::Unsatisfiable)?;

        // Determine the order of hashing based on the bit value.
        let hash_order = if b {
            vec![sibling_hash.to_owned(), actual_root_hash]
        } else {
            vec![actual_root_hash, sibling_hash.to_owned()]
        };

        // Compute the new hash.
        actual_root_hash = GD::digest(
            cs.namespace(|| format!("sibling {}", i)),
            &hash_order.concat(),
        )?;
    }

    hash_equality(cs, &expected_root, actual_root_hash)
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
    expected: &HashValue,
    actual: HashValue,
) -> Result<HashValue, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    if expected.len() != actual.len() {
        return Err(SynthesisError::Unsatisfiable);
    }

    // Check if the reconstructed root hash matches the expected root hash
    for i in 0..expected.len() {
        Boolean::enforce_equal(
            cs.namespace(|| format!("equality on {} hash bit", i)),
            &expected[i],
            &actual[i],
        )?;
    }

    Ok(actual)
}
