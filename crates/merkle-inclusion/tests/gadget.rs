use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_keccak::{keccak256, sha3};
use bellpepper_merkle_inclusion::traits::GadgetDigest;
use bellpepper_merkle_inclusion::{create_gadget_digest_impl, verify_proof, Leaf, Proof};
use bellpepper_sha512::sha512::sha512;
use bitvec::order::{BitOrder, Lsb0, Msb0};
use bitvec::prelude::BitVec;
use bls12_381::{Bls12, Scalar};
use digest::{Digest, Output};
use ff::PrimeField;
use pairing::Engine;
use sha2::Sha512 as rSha512;
use sha3::{Keccak256, Sha3_256};

// Example use of the macro with OutOfCircuitHasher specified
create_gadget_digest_impl!(Sha3, sha3, 32, Sha3_256, true);
create_gadget_digest_impl!(Keccak, keccak256, 32, Keccak256, true);
create_gadget_digest_impl!(Sha512, sha512, 64, rSha512, false);
// Utility to help us in calculated expected number of constraints for the hashing circuit.
const SHA3_CONSTRAINTS: usize = 151424;
const SHA_512_CONSTRAINTS: usize = 113105;

fn expected_circuit_constraints<GD: GadgetDigest<Scalar>>(
    hasher_constraints: usize,
    nbr_siblings: usize,
) -> usize {
    3 * GD::output_size() * 8 + (GD::output_size() * 8 + hasher_constraints + 1) * nbr_siblings
}

fn verify_inclusion_merkle<GD: GadgetDigest<Scalar>, O: BitOrder>() {
    // Construct the Merkle tree
    let simple_tree = construct_merkle_tree::<GD>();

    // Get key for d
    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();

    let proof = Proof::new(
        Leaf::new(
            simple_tree.get_leaf_key(1).to_vec(),
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(1)),
        ),
        vec![
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(0)),
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(9)),
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(13)),
        ],
    );

    let res = verify_proof::<_, _, GD>(cs, bytes_to_bitvec::<O>(simple_tree.root()), proof);

    assert_eq!(
        bits_to_bytevec::<O>(&res.unwrap()),
        simple_tree.root().to_vec(),
        "The root hash must match the expected root hash."
    );
}

fn verify_non_existing_leaf<GD: GadgetDigest<Scalar>, O: BitOrder>() {
    // Construct the Merkle tree
    let simple_tree = construct_merkle_tree::<GD>();

    let mut non_existing_key: Vec<Boolean> = Vec::with_capacity(GD::OUTPUT_SIZE * 8);
    for _ in 0..<GD as GadgetDigest<Scalar>>::OUTPUT_SIZE * 8 {
        non_existing_key.push(Boolean::constant(false));
    }

    let non_existing_leaf_hash =
        hash::<<GD as GadgetDigest<Scalar>>::OutOfCircuitHasher>(b"non_existing").to_vec();

    let proof = Proof::new(
        Leaf::new(
            non_existing_key.to_vec(),
            bytes_to_bitvec::<O>(&non_existing_leaf_hash),
        ),
        vec![/* sibling hashes */],
    );

    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
    let res = verify_proof::<_, _, GD>(cs, bytes_to_bitvec::<O>(simple_tree.root()), proof);

    assert!(
        res.is_err(),
        "Proof verification should fail for a non-existing leaf."
    );
}

fn verify_incorrect_sibling_hashes<GD: GadgetDigest<Scalar>, O: BitOrder>() {
    // Construct the Merkle tree
    let simple_tree = construct_merkle_tree::<GD>();

    let incorrect_sibling =
        hash::<<GD as GadgetDigest<Scalar>>::OutOfCircuitHasher>(b"incorrect").to_vec();

    let proof = Proof::new(
        Leaf::new(
            simple_tree.get_leaf_key(0).to_vec(),
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(0)),
        ),
        vec![
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(1)),
            bytes_to_bitvec::<O>(&incorrect_sibling), // incorrect sibling hash
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(13)),
        ],
    );

    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
    let res = verify_proof::<_, _, GD>(cs, bytes_to_bitvec::<O>(simple_tree.root()), proof);

    assert!(
        res.is_err(),
        "Proof verification should fail with incorrect sibling hashes."
    );
}

fn verify_single_leaf_merkle<GD: GadgetDigest<Scalar>, O: BitOrder>() {
    // Single leaf Merkle tree (root is the leaf itself)
    let single_leaf =
        hash::<<GD as GadgetDigest<Scalar>>::OutOfCircuitHasher>(b"single_leaf").to_vec();

    let mut leaf_key: Vec<Boolean> = Vec::with_capacity(GD::OUTPUT_SIZE * 8);
    for _ in 0..GD::OUTPUT_SIZE * 8 {
        leaf_key.push(Boolean::constant(false));
    }

    let proof = Proof::new(
        Leaf::new(leaf_key.to_vec(), bytes_to_bitvec::<O>(&single_leaf)),
        vec![], // No siblings in a single-leaf tree
    );

    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
    let res = verify_proof::<_, _, GD>(cs, bytes_to_bitvec::<O>(&single_leaf), proof);

    assert!(
        res.is_ok(),
        "Proof verification should succeed for a single-leaf Merkle tree."
    );
    assert_eq!(
        bits_to_bytevec::<O>(&res.unwrap()),
        single_leaf.to_vec(),
        "The root hash must match the single leaf hash."
    );
}

fn check_number_constraints<GD: GadgetDigest<Scalar>, O: BitOrder>(hasher_constraints: usize) {
    // Construct the Merkle tree
    let simple_tree = construct_merkle_tree::<GD>();

    // Get key for d
    let mut cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();

    let proof = Proof::new(
        Leaf::new(
            simple_tree
                .get_leaf_key(0)
                .to_vec()
                .iter()
                .enumerate()
                .map(|(i, b)| {
                    // Only the 3 first bits need to be allocated.
                    if i < 3 {
                        return Boolean::from(
                            AllocatedBit::alloc(
                                cs.namespace(|| format!("leaf_key bit {}", i)),
                                b.get_value(),
                            )
                            .unwrap(),
                        );
                    } else {
                        Boolean::Constant(false)
                    }
                })
                .collect(),
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(0))
                .iter()
                .enumerate()
                .map(|(i, b)| {
                    Boolean::from(
                        AllocatedBit::alloc(
                            cs.namespace(|| format!("leaf_hash bit {}", i)),
                            b.get_value(),
                        )
                        .unwrap(),
                    )
                })
                .collect(),
        ),
        vec![
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(1))
                .iter()
                .enumerate()
                .map(|(i, b)| {
                    Boolean::from(
                        AllocatedBit::alloc(
                            cs.namespace(|| format!("first_sibling bit {}", i)),
                            b.get_value(),
                        )
                        .unwrap(),
                    )
                })
                .collect(),
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(9))
                .iter()
                .enumerate()
                .map(|(i, b)| {
                    Boolean::from(
                        AllocatedBit::alloc(
                            cs.namespace(|| format!("second_sibling bit {}", i)),
                            b.get_value(),
                        )
                        .unwrap(),
                    )
                })
                .collect(),
            bytes_to_bitvec::<O>(simple_tree.get_leaf_hash(13))
                .iter()
                .enumerate()
                .map(|(i, b)| {
                    Boolean::from(
                        AllocatedBit::alloc(
                            cs.namespace(|| format!("third_sibling bit {}", i)),
                            b.get_value(),
                        )
                        .unwrap(),
                    )
                })
                .collect(),
        ],
    );

    let constrained_expected_root: Vec<Boolean> = bytes_to_bitvec::<O>(simple_tree.root())
        .iter()
        .enumerate()
        .map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(
                    cs.namespace(|| format!("expected_root bit {}", i)),
                    b.get_value(),
                )
                .unwrap(),
            )
        })
        .collect();

    let res = verify_proof::<_, _, GD>(
        cs.namespace(|| "verify_proof"),
        constrained_expected_root,
        proof.clone(),
    );

    assert_eq!(
        bits_to_bytevec::<O>(&res.unwrap()),
        simple_tree.root().to_vec(),
        "The root hash must match the expected root hash."
    );

    assert!(cs.is_satisfied(), "CS should be satisfied, but it is not.");

    assert_eq!(
        cs.num_constraints(),
        expected_circuit_constraints::<GD>(hasher_constraints, proof.siblings().len()),
        "Expected {} constraints, got {}",
        expected_circuit_constraints::<GD>(hasher_constraints, proof.siblings().len()),
        cs.num_constraints()
    );
}

#[test]
fn test_verify_inclusion_merkle() {
    verify_inclusion_merkle::<Sha3, Lsb0>();
    verify_inclusion_merkle::<Keccak, Lsb0>();
    verify_inclusion_merkle::<Sha512, Msb0>();
}
#[test]
fn test_verify_non_existing_leaf() {
    verify_non_existing_leaf::<Sha3, Lsb0>();
    verify_non_existing_leaf::<Keccak, Lsb0>();
    verify_non_existing_leaf::<Sha512, Msb0>();
}
#[test]
fn test_verify_incorrect_sibling_hashes() {
    verify_incorrect_sibling_hashes::<Sha3, Lsb0>();
    verify_incorrect_sibling_hashes::<Keccak, Lsb0>();
    verify_incorrect_sibling_hashes::<Sha512, Msb0>();
}
#[test]
fn test_verify_single_leaf_merkle() {
    verify_single_leaf_merkle::<Sha3, Lsb0>();
    verify_single_leaf_merkle::<Keccak, Lsb0>();
    verify_single_leaf_merkle::<Sha512, Msb0>();
}
#[test]
fn test_check_number_constraints() {
    check_number_constraints::<Sha3, Lsb0>(SHA3_CONSTRAINTS);
    check_number_constraints::<Keccak, Lsb0>(SHA3_CONSTRAINTS);
    check_number_constraints::<Sha512, Msb0>(SHA_512_CONSTRAINTS);
}

/**************************************************************
 * Utilities
 **************************************************************/

pub fn bytes_to_bitvec<O: BitOrder>(bytes: &[u8]) -> Vec<Boolean> {
    let bits = BitVec::<u8, O>::from_slice(bytes);
    bits.iter().map(|b| Boolean::constant(*b)).collect()
}

pub fn bits_to_bytevec<O: BitOrder>(bits: &[Boolean]) -> Vec<u8> {
    let mut bv = BitVec::<u8, O>::new();
    bv.extend(bits.iter().map(|b| b.get_value().unwrap()));
    bv.as_raw_slice().to_vec()
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
/// The path keys are long as specified by the referred Digest output size bits long, padded with `false` values.
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
pub fn construct_merkle_tree<GD: GadgetDigest<Scalar>>() -> SimpleMerkleTree {
    let predefined_leaves = [b"a", b"b", b"c", b"d", b"e", b"f", b"g", b"h"]
        .iter()
        .map(|d| hash::<GD::OutOfCircuitHasher>(d.to_owned()).to_vec())
        .collect::<Vec<Vec<u8>>>();

    let mut leaves = predefined_leaves.clone();

    for j in (0..12).step_by(2) {
        leaves.push(
            hash::<GD::OutOfCircuitHasher>(
                &[leaves[j].to_owned(), leaves[j + 1].to_owned()].concat(),
            )
            .to_vec(),
        );
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

        // Reverse based on endianness, because we always read the key from MSB (bottom) to LSB (root)
        if GD::is_little_endian() {
            path.reverse();
        }

        // Pad the path to ensure it's sized as Digest output
        while path.len() < <GD::OutOfCircuitHasher as Digest>::output_size() * 8 {
            path.push(Boolean::constant(false));
        }

        leaf_key_vec.push((item.to_owned(), path));
    }

    // Compute expected root hash
    let expected_root =
        hash::<GD::OutOfCircuitHasher>(&[leaves[12].to_owned(), leaves[13].to_owned()].concat())
            .to_vec();

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
