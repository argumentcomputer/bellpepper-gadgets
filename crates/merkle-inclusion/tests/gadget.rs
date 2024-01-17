use bellpepper_core::boolean::Boolean;
use bellpepper_core::test_cs::TestConstraintSystem;
use bls12_381::Bls12;

use crate::utils;
use crate::utils::sha3;
use bellpepper_merkle_inclusion::{verify_proof, Leaf, Proof};
use pairing::Engine;

#[test]
fn test_verify_inclusion_merkle() {
    // Construct the Merkle tree
    let (root, leaves) = utils::construct_merkle_tree();

    // Get key for d
    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();

    let proof = Proof::new(
        Leaf::new(
            leaves.get(0).unwrap().1.to_vec(),
            utils::bytes_to_bitvec(&leaves.get(0).unwrap().0),
        ),
        vec![
            utils::bytes_to_bitvec(&leaves.get(1).unwrap().0),
            utils::bytes_to_bitvec(&leaves.get(9).unwrap().0),
            utils::bytes_to_bitvec(&leaves.get(13).unwrap().0),
        ],
    );

    let res = verify_proof::<_, _, bellpepper_merkle_inclusion::traits::Sha3>(
        cs,
        utils::bytes_to_bitvec(&root),
        proof,
    );

    assert_eq!(
        utils::bits_to_bytevec(&res.unwrap()),
        root.to_vec(),
        "The root hash must match the expected root hash."
    );
}

#[test]
fn test_verify_non_existing_leaf() {
    // Construct the Merkle tree
    let (root, _) = utils::construct_merkle_tree();

    let non_existing_key = [false; 256].map(|b| Boolean::constant(b));
    let non_existing_leaf_hash = utils::sha3(b"non_existing");

    let proof = Proof::new(
        Leaf::new(
            non_existing_key.to_vec(),
            utils::bytes_to_bitvec(&non_existing_leaf_hash),
        ),
        vec![/* sibling hashes */],
    );

    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
    let res = verify_proof::<_, _, bellpepper_merkle_inclusion::traits::Sha3>(
        cs,
        utils::bytes_to_bitvec(&root),
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
    let (root, leaves) = utils::construct_merkle_tree();

    let incorrect_sibling = utils::sha3(b"incorrect");

    let proof = Proof::new(
        Leaf::new(
            leaves.get(0).unwrap().1.to_vec(),
            utils::bytes_to_bitvec(&leaves.get(0).unwrap().0),
        ),
        vec![
            utils::bytes_to_bitvec(&leaves.get(1).unwrap().0),
            utils::bytes_to_bitvec(&incorrect_sibling), // incorrect sibling hash
            utils::bytes_to_bitvec(&leaves.get(13).unwrap().0),
        ],
    );

    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
    let res = verify_proof::<_, _, bellpepper_merkle_inclusion::traits::Sha3>(
        cs,
        utils::bytes_to_bitvec(&root),
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
    let single_leaf = sha3(b"single_leaf".as_slice());

    let leaf_key = [false; 256].map(|b| Boolean::constant(b));
    let proof = Proof::new(
        Leaf::new(leaf_key.to_vec(), utils::bytes_to_bitvec(&single_leaf)),
        vec![], // No siblings in a single-leaf tree
    );

    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
    let res = verify_proof::<_, _, bellpepper_merkle_inclusion::traits::Sha3>(
        cs,
        utils::bytes_to_bitvec(&single_leaf),
        proof,
    );

    assert!(
        res.is_ok(),
        "Proof verification should succeed for a single-leaf Merkle tree."
    );
    assert_eq!(
        utils::bits_to_bytevec(&res.unwrap()),
        single_leaf.to_vec(),
        "The root hash must match the single leaf hash."
    );
}
