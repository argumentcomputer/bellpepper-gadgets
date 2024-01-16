pub mod traits;

use crate::traits::GadgetDigest;
use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_keccak::sha3;
use ff::PrimeField;

// HashValue represents the digest type output from the hash function
pub type HashValue = Vec<Boolean>;
pub type Key = Vec<Boolean>;
const HASH_LENGTH: usize = 32 * 8;

// Leaf structure represents a leaf node in the Jellyfish Merkle Tree
pub struct Leaf {
    key: Key,
    value_hash: HashValue,
}

impl Leaf {
    pub fn hash(&self) -> &HashValue {
        &self.value_hash
    }

    pub fn key(&self) -> &HashValue {
        &self.key
    }
}

// Proof structure contains a leaf node and sibling hashes for proof verification
pub struct Proof {
    leaf: Leaf,
    siblings: Vec<HashValue>,
}

impl Proof {
    pub fn leaf(&self) -> &Leaf {
        &self.leaf
    }

    pub fn siblings(&self) -> &[Vec<Boolean>] {
        &self.siblings
    }
}

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
    // Length of input is 256*3*nbr_siblings = 256 (expected_root) + 256 (proof_leaf_key) + 256 (proof_leaf_hash_value) + 256 * nbr_siblings
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
