use bellpepper_core::boolean::Boolean;
use bellpepper_core::test_cs::TestConstraintSystem;
use bls12_381::Bls12;

use bitvec::prelude::*;
use pairing::Engine;
use tiny_keccak::{Hasher, Sha3};

use bellpepper_merkle_inclusion::verify_proof;

fn sha3(preimage: &[u8]) -> [u8; 32] {
    let mut sha3 = Sha3::v256();

    sha3.update(preimage);

    let mut hash = [0u8; 32];
    sha3.finalize(&mut hash);
    hash
}

fn bytes_to_bitvec(bytes: &[u8]) -> Vec<Boolean> {
    let bits = BitVec::<Lsb0, u8>::from_slice(bytes);
    let bits: Vec<Boolean> = bits.iter().map(|b| Boolean::constant(*b)).collect();
    bits
}

fn bits_to_bytevec(bits: &[Boolean]) -> Vec<u8> {
    let result: Vec<bool> = bits.iter().map(|b| b.get_value().unwrap()).collect();
    let mut bv = BitVec::<Lsb0, u8>::new();
    for bit in result {
        bv.push(bit);
    }
    bv.as_slice().to_vec()
}

#[test]
fn test_verify_empty_sparse_merkle() {
    //            root
    //           /    \
    //          a      b
    //                / \
    //               c   d
    //              / \
    //             e   f
    // f key: 101
    let a = sha3(b"a");
    let d = sha3(b"d");
    let e = sha3(b"e");
    let f = sha3(b"f");

    let c = sha3(&[e, f].concat());
    let b = sha3(&[c, d].concat());
    let root = sha3(&[a, b].concat());

    let mut key = [false; 256].map(|b| Boolean::constant(b));
    key[0] = Boolean::Constant(true);
    key[2] = Boolean::Constant(true);

    let payload = [
        bytes_to_bitvec(&root),
        key.to_vec(),
        bytes_to_bitvec(&f),
        bytes_to_bitvec(&e),
        bytes_to_bitvec(&d),
        bytes_to_bitvec(&a),
    ]
    .concat()
    .to_vec();

    let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();

    let res = verify_proof::<_, _, bellpepper_merkle_inclusion::traits::Sha3>(cs, &payload);
    dbg!(&res);
    assert_eq!(bits_to_bytevec(&res.unwrap()), root.to_vec());
}
