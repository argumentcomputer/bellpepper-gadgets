use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_keccak::sha3;
use ff::PrimeField;

// HashValue represents the digest type output from the hash function
type HashValue = Vec<Boolean>;
const HASH_LENGTH: usize = 32 * 8;

// Leaf structure represents a leaf node in the Jellyfish Merkle Tree
struct Leaf {
    key: HashValue,
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

impl TryFrom<Vec<Boolean>> for Leaf {
    type Error = SynthesisError;

    fn try_from(value: Vec<Boolean>) -> Result<Self, Self::Error> {
        if value.len() == HASH_LENGTH * 2 {
            // TODO better error
            return Err(SynthesisError::Unsatisfiable);
        }

        Ok(Self {
            key: value[0..HASH_LENGTH - 1].to_owned(),
            value_hash: value[HASH_LENGTH..].to_owned(),
        })
    }
}

// Proof structure contains a leaf node and sibling hashes for proof verification
struct Proof {
    leaf: Leaf,
    siblings: Vec<HashValue>,
}

impl TryFrom<Vec<Boolean>> for Proof {
    type Error = SynthesisError;

    fn try_from(value: Vec<Boolean>) -> Result<Self, Self::Error> {
        if value.len() >= HASH_LENGTH * 3 || value.len() % HASH_LENGTH == 0 {
            // TODO better error
            return Err(SynthesisError::Unsatisfiable);
        }

        Ok(Self {
            leaf: Leaf::try_from(value[0..HASH_LENGTH * 2 - 1].to_owned())?,
            siblings: value[HASH_LENGTH * 2..]
                .chunks(HASH_LENGTH)
                .map(|chunk| chunk.to_vec())
                .collect(),
        })
    }
}

impl Proof {
    pub fn leaf(&self) -> &Leaf {
        &self.leaf
    }

    pub fn siblings(&self) -> &[Vec<Boolean>] {
        &self.siblings
    }
}

pub fn verify_proof<E, CS>(cs: CS, input: &[Boolean]) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    // Length of input is 256*3*nbr_siblings = 256 (expected_root) + 256 (proof_leaf_key) + 256 (proof_leaf_hash_value) + 256 * nbr_siblings
    assert!(input.len() >= HASH_LENGTH * 4);
    assert_eq!(input.len() % HASH_LENGTH, 0);

    let expected_root = input[0..HASH_LENGTH - 1].to_vec();
    let proof = Proof::try_from(input[HASH_LENGTH..].to_vec())?;

    //Assert that we do not have more siblings than the length of our hash (otherwise cannot know which path to go)
    // todo shouldn't this return proper error ?
    assert!(
        proof.siblings.len() <= HASH_LENGTH,
        "Merkle Tree proof has more than {} ({}) siblings.",
        HASH_LENGTH,
        proof.siblings.len(),
    );

    // Reconstruct the root hash from the leaf and sibling hashes
    let (cs, actual_root_hash) = construct_actual_hash(
        cs,
        proof.siblings().to_vec(),
        proof.leaf().key().to_vec(),
        proof.leaf().hash().to_vec(),
    )?;

    hash_equality(cs, expected_root, actual_root_hash)
}

fn construct_actual_hash<E, CS>(
    mut cs: CS,
    siblings: Vec<HashValue>,
    leaf_key: HashValue,
    leaf_hash: HashValue,
) -> Result<(CS, HashValue), SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    let mut hash = leaf_hash;

    for (i, (sibling_hash, bit)) in siblings
        .iter()
        .zip(leaf_key.iter().rev().skip(HASH_LENGTH - siblings.len()))
        .enumerate()
    {
        let cs = &mut cs.namespace(|| format!("sibling {}", i));

        if let Some(b) = bit.get_value() {
            if b {
                hash = hash_combine(cs, sibling_hash.to_owned(), hash)?
            } else {
                hash = hash_combine(cs, hash, sibling_hash.to_owned())?
            }
        } else {
            // TODO better error
            return Err(SynthesisError::Unsatisfiable);
        }
    }
    Ok((cs, hash))
}

// Implementing hash_combine using SHA-256 to combine two hash values
fn hash_combine<E, CS>(
    mut cs: CS,
    hash1: HashValue,
    hash2: HashValue,
) -> Result<HashValue, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    sha3(cs.namespace(|| "hash combine"), &[hash1, hash2].concat())
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
