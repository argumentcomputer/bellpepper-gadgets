use bellpepper_core::boolean::Boolean;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::ConstraintSystem;
use bls12_381::Bls12;

use bitvec::prelude::*;
use pairing::Engine;
use tiny_keccak::{Hasher, Keccak, Sha3};

use proptest::prelude::*;

use bellpepper_keccak::keccak256 as keccak_gadget;
use bellpepper_keccak::sha3 as sha3_gadget;
use libsecp256k1::{PublicKey, SecretKey};

fn keccak256(preimage: &[u8]) -> [u8; 32] {
    let mut keccak = Keccak::v256();

    keccak.update(preimage);

    let mut hash = [0u8; 32];
    keccak.finalize(&mut hash);
    hash
}

fn sha3(preimage: &[u8]) -> [u8; 32] {
    let mut sha3 = Sha3::v256();

    sha3.update(preimage);

    let mut hash = [0u8; 32];
    sha3.finalize(&mut hash);
    hash
}

fn bytes_to_bitvec(bytes: &[u8]) -> Vec<Boolean> {
    let bits = BitVec::<u8, Lsb0>::from_slice(bytes);
    let bits: Vec<Boolean> = bits.iter().map(|b| Boolean::constant(*b)).collect();
    bits
}

fn bits_to_bytevec(bits: &[Boolean]) -> Vec<u8> {
    let result: Vec<bool> = bits.iter().map(|b| b.get_value().unwrap()).collect();
    let mut bv = BitVec::<u8, Lsb0>::new();
    for bit in result {
        bv.push(bit);
    }
    bv.as_raw_slice().to_vec()
}

proptest! {
    #[test]
    fn test_keccak256(preimage in "[0-9a-f]{128}") {
        let preimage = hex::decode(preimage).unwrap();
        let expected = keccak256(&preimage);

        let preimage = bytes_to_bitvec(&preimage);

        let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
        let result = keccak_gadget(cs, &preimage).unwrap();

        let result = bits_to_bytevec(&result);

        assert_eq!(hex::encode(result), hex::encode(expected));
    }
}

proptest! {
    #[test]
    fn test_sha3(preimage in "[0-9a-f]{128}") {
        let preimage = hex::decode(preimage).unwrap();
        let expected = sha3(&preimage);

        let preimage = bytes_to_bitvec(&preimage);

        let cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();
        let result = sha3_gadget(cs, &preimage).unwrap();

        let result = bits_to_bytevec(&result);

        assert_eq!(hex::encode(result), hex::encode(expected));
    }
}

#[test]
fn test_ethereum_addresses() {
    let mut cs = TestConstraintSystem::<<Bls12 as Engine>::Fr>::new();

    // mnemonic:	"into trim cross then helmet popular suit hammer cart shrug oval student"
    // seed:		ca5a4407934514911183f0c4ffd71674ab28028c060c15d270977ba57c390771
    //              967ab84ed473702fef5eb36add05ea590d99ddff14c730e93ad14b418a2788b8
    // private key:	d6840b79c2eb1f5ff97a41590df3e04d7d4b0965073ff2a9fbb7ff003799dc71
    // address:	    0x604a95C9165Bc95aE016a5299dd7d400dDDBEa9A
    let skey = SecretKey::parse_slice(
        &hex::decode("d6840b79c2eb1f5ff97a41590df3e04d7d4b0965073ff2a9fbb7ff003799dc71").unwrap(),
    )
    .unwrap();
    let pkey = PublicKey::from_secret_key(&skey);
    let full_public_key = pkey.serialize();
    let address = keccak256(&full_public_key[1..]);
    assert_eq!(
        hex::encode(&address[12..]),
        "604a95c9165bc95ae016a5299dd7d400dddbea9a"
    );

    let raw_public_key = bytes_to_bitvec(&full_public_key[1..]);
    let address = keccak_gadget(cs.namespace(|| "addr 1"), &raw_public_key).unwrap();
    let address = bits_to_bytevec(&address);
    assert_eq!(
        hex::encode(&address[12..]),
        "604a95c9165bc95ae016a5299dd7d400dddbea9a"
    );

    // mnemonic:	"finish oppose decorate face calm tragic certain desk hour urge dinosaur mango"
    // seed:		7d34eb533ad9fea340cd93d82b8baead0c00a81380caa682aca06631fe851a63
    //              093db5cb5c81b3009a0281b2c34959750bbb5dfaab219d17f04f1a1b37b93400
    // private key:	d3cc16948a02a91b9fcf83735653bf3dfd82c86543fdd1e9a828bd25e8a7b68d
    // address:	    0x1c96099350f13D558464eC79B9bE4445AA0eF579
    let skey = SecretKey::parse_slice(
        &hex::decode("d3cc16948a02a91b9fcf83735653bf3dfd82c86543fdd1e9a828bd25e8a7b68d").unwrap(),
    )
    .unwrap();
    let pkey = PublicKey::from_secret_key(&skey);
    let full_public_key = pkey.serialize();
    let address = keccak256(&full_public_key[1..]);
    assert_eq!(
        hex::encode(&address[12..]),
        "1c96099350f13d558464ec79b9be4445aa0ef579"
    );

    let raw_public_key = bytes_to_bitvec(&full_public_key[1..]);
    let address = keccak_gadget(cs.namespace(|| "addr 2"), &raw_public_key).unwrap();
    let address = bits_to_bytevec(&address);
    assert_eq!(
        hex::encode(&address[12..]),
        "1c96099350f13d558464ec79b9be4445aa0ef579"
    );
}
