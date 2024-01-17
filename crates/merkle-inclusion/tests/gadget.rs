use bellpepper_core::boolean::Boolean;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_merkle_inclusion::traits::{GadgetDigest, Keccak, Sha3};
use bellpepper_merkle_inclusion::{verify_proof, Leaf, Proof};
use bitvec::order::Lsb0;
use bitvec::prelude::BitVec;
use bls12_381::{Bls12, Scalar};
use digest::{Digest, Output};
use pairing::Engine;

macro_rules! create_hash_tests {
    ($test_name_suffix:ident, $hash_struct:ident) => {
        mod $test_name_suffix {
            use super::*;

            #[test]
            fn test_verify_inclusion_merkle() {
                // Construct the Merkle tree
                let simple_tree = construct_merkle_tree::<
                    <$hash_struct as GadgetDigest<Scalar>>::OutOfCircuitHasher,
                >();

                // Get key for d
                let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();

                let proof = Proof::new(
                    Leaf::new(
                        simple_tree.get_leaf_key(0).to_vec(),
                        bytes_to_bitvec(simple_tree.get_leaf_hash(0)),
                    ),
                    vec![
                        bytes_to_bitvec(simple_tree.get_leaf_hash(1)),
                        bytes_to_bitvec(simple_tree.get_leaf_hash(9)),
                        bytes_to_bitvec(simple_tree.get_leaf_hash(13)),
                    ],
                );

                let res = verify_proof::<_, _, $hash_struct>(
                    cs,
                    bytes_to_bitvec(simple_tree.root()),
                    proof,
                );

                assert_eq!(
                    bits_to_bytevec(&res.unwrap()),
                    simple_tree.root().to_vec(),
                    "The root hash must match the expected root hash."
                );
            }

            #[test]
            fn test_verify_non_existing_leaf() {
                // Construct the Merkle tree
                let simple_tree = construct_merkle_tree::<
                    <$hash_struct as GadgetDigest<Scalar>>::OutOfCircuitHasher,
                >();

                let non_existing_key = [false; 256].map(|b| Boolean::constant(b));
                let non_existing_leaf_hash = hash::<
                    <$hash_struct as GadgetDigest<Scalar>>::OutOfCircuitHasher,
                >(b"non_existing").to_vec();

                let proof = Proof::new(
                    Leaf::new(
                        non_existing_key.to_vec(),
                        bytes_to_bitvec(&non_existing_leaf_hash),
                    ),
                    vec![/* sibling hashes */],
                );

                let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
                let res = verify_proof::<_, _, $hash_struct>(
                    cs,
                    bytes_to_bitvec(&simple_tree.root()),
                    proof,
                );

                assert!(
                    res.is_err(),
                    "Proof verification should fail for a non-existing leaf."
                );
            }

            #[test]
            fn test_verify_incorrect_sibling_hashes() {
                // Construct the Merkle tree
                let simple_tree = construct_merkle_tree::<
                    <$hash_struct as GadgetDigest<Scalar>>::OutOfCircuitHasher,
                >();

                let incorrect_sibling = hash::<
                    <$hash_struct as GadgetDigest<Scalar>>::OutOfCircuitHasher,
                >(b"incorrect").to_vec();

                let proof = Proof::new(
                    Leaf::new(
                        simple_tree.get_leaf_key(0).to_vec(),
                        bytes_to_bitvec(simple_tree.get_leaf_hash(0)),
                    ),
                    vec![
                        bytes_to_bitvec(simple_tree.get_leaf_hash(1)),
                        bytes_to_bitvec(&incorrect_sibling), // incorrect sibling hash
                        bytes_to_bitvec(simple_tree.get_leaf_hash(13)),
                    ],
                );

                let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
                let res = verify_proof::<_, _, $hash_struct>(
                    cs,
                    bytes_to_bitvec(simple_tree.root()),
                    proof,
                );

                assert!(
                    res.is_err(),
                    "Proof verification should fail with incorrect sibling hashes."
                );
            }

            #[test]
            fn test_verify_single_leaf_merkle() {
                // Single leaf Merkle tree (root is the leaf itself)
                let single_leaf = hash::<
                    <$hash_struct as GadgetDigest<Scalar>>::OutOfCircuitHasher,
                >(b"single_leaf")
                .to_vec();

                let leaf_key = [false; 256].map(|b| Boolean::constant(b));
                let proof = Proof::new(
                    Leaf::new(leaf_key.to_vec(), bytes_to_bitvec(&single_leaf)),
                    vec![], // No siblings in a single-leaf tree
                );

                let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
                let res = verify_proof::<_, _, $hash_struct>(
                    cs,
                    bytes_to_bitvec(&single_leaf),
                    proof,
                );

                assert!(
                    res.is_ok(),
                    "Proof verification should succeed for a single-leaf Merkle tree."
                );
                assert_eq!(
                    bits_to_bytevec(&res.unwrap()),
                    single_leaf.to_vec(),
                    "The root hash must match the single leaf hash."
                );
            }
        }
    };
}

// Generate tests for Sha3 and Keccak with lowercase suffixes
create_hash_tests!(sha3, Sha3);
create_hash_tests!(keccak, Keccak);

/**************************************************************
 * Utilities
 **************************************************************/

pub fn bytes_to_bitvec(bytes: &[u8]) -> Vec<Boolean> {
    let bits = BitVec::<Lsb0, u8>::from_slice(bytes);
    let bits: Vec<Boolean> = bits.iter().map(|b| Boolean::constant(*b)).collect();
    bits
}

pub fn bits_to_bytevec(bits: &[Boolean]) -> Vec<u8> {
    let result: Vec<bool> = bits.iter().map(|b| b.get_value().unwrap()).collect();
    let mut bv = BitVec::<Lsb0, u8>::new();
    for bit in result {
        bv.push(bit);
    }
    bv.as_slice().to_vec()
}

pub struct SimpleMerkleTree {
    root: Vec<u8>,
    leaf_key_vec: Vec<(Vec<u8>, Vec<Boolean>)>,
}

impl SimpleMerkleTree {
    pub fn get_leaf_key(&self, index: usize) -> &[Boolean] {
        &self.leaf_key_vec.get(index).unwrap().1
    }

    pub fn get_leaf_hash(&self, index: usize) -> &[u8] {
        &self.leaf_key_vec.get(index).unwrap().0
    }

    pub fn root(&self) -> &[u8] {
        &self.root
    }
}

/// Constructs a fixed-depth binary Merkle tree with predefined leaf values.
///
/// This function creates a Merkle tree with a depth of 4 (including the root).
/// The leaves of the tree are the SHA3 hashes of the predefined values: "a", "b", "c", "d", "e", "f", "g", "h".
/// It computes the hash and path key for each leaf and intermediary node.
///
/// # Returns
/// A tuple containing:
/// - The root hash of the Merkle tree as the first element.
/// - A vector of tuples, each containing:
///   - The hash of a leaf or intermediary node.
///   - The path key, a `Vec<Boolean>`, representing the path from the root to the node.
///
/// # Path Key Representation
/// The path key is a vector of `Boolean` values, where each value indicates a direction at a node:
/// - `Boolean::constant(false)` for a left turn.
/// - `Boolean::constant(true)` for a right turn.
/// The path keys are 256 bits long, padded with `false` values.
///
/// # Tree Structure
/// The tree structure is as follows (indexes in the vector are shown in parentheses):
/// ```plaintext
///         root
///        /    \
///      (12)   (13)
///      /  \    /  \
///    (8) (9) (10) (11)
///    / \  / \  / \  / \
///  (0)(1)(2)(3)(4)(5)(6)(7)
///   a  b  c  d  e  f  g  h
/// ```
/// In this structure:
/// - Leaf nodes ("a" to "h") are at indexes 0 to 7.
/// - Intermediary nodes are at indexes 8 to 13.
/// - The root node is at index 14.
///
/// # Example
/// ```
/// let (root_hash, leaf_hashes_and_keys) = construct_merkle_tree();
/// for (hash, key) in leaf_hashes_and_keys.iter() {
///     // Process each leaf and intermediary node's hash and key...
/// }
/// ```
pub fn construct_merkle_tree<D: Digest>() -> SimpleMerkleTree {
    let predefined_leaves = [b"a", b"b", b"c", b"d", b"e", b"f", b"g", b"h"]
        .iter()
        .map(|d| hash::<D>(d.to_owned()).to_vec())
        .collect::<Vec<Vec<u8>>>();

    let mut leaves = predefined_leaves.clone();

    for j in (0..12).step_by(2) {
        leaves.push(hash::<D>(&[leaves[j].to_owned(), leaves[j + 1].to_owned()].concat()).to_vec());
    }
    // Generate keys
    let mut leaf_key_vec = Vec::new();
    for (i, item) in leaves.iter().enumerate().take(14) {
        let mut path = Vec::new();
        let mut node_index = i;
        let depth = if i <= 7 {
            3
        } else if i < 12 {
            2
        } else {
            1
        };

        for _ in 0..depth {
            let direction = (node_index & 1) != 0; // Right if odd, Left if even
            path.push(Boolean::constant(direction));
            node_index >>= 1;
        }

        // Reverse to get the path from root to the node
        path.reverse();

        // Pad the path to ensure it's 256 elements long
        while path.len() < 256 {
            path.push(Boolean::constant(false));
        }
        leaf_key_vec.push((item.to_owned(), path));
    }

    // Compute expected root hash
    let expected_root =
        hash::<D>(&[leaves[12].to_owned(), leaves[13].to_owned()].concat()).to_vec();

    SimpleMerkleTree {
        root: expected_root.to_owned(),
        leaf_key_vec,
    }
}

pub fn hash<D: Digest>(data: &[u8]) -> Output<D> {
    let mut hasher = D::new();
    hasher.update(data);

    hasher.finalize()
}
