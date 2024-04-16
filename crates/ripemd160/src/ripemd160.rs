//! Circuits for the [RIPEMD-160] hash function and its internal compression
//! function.
//!
//! [RIPEMD-160]: https://homes.esat.kuleuven.be/~bosselae/ripemd160.html

use bellpepper::gadgets::{multieq::MultiEq, uint32::UInt32};
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use std::{convert::TryInto, iter};

use crate::util::{f1, f2, f3, f4, f5, uint32_rotl};

const IV: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
const ROUND_CONSTANTS_LEFT: [u32; 5] = [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e];
const ROUND_CONSTANTS_RIGHT: [u32; 5] =
    [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000];

pub const MSG_SEL_IDX_LEFT: [usize; 80] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5,
    2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4,
    13, 3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
];
pub const MSG_SEL_IDX_RIGHT: [usize; 80] = [
    5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12,
    4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5,
    12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
];

pub const ROL_AMOUNT_LEFT: [usize; 80] = [
    11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15,
    9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14,
    15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
];
pub const ROL_AMOUNT_RIGHT: [usize; 80] = [
    8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12,
    7, 6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14,
    6, 14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
];

pub fn ripemd160<Scalar, CS>(cs: CS, input: &[Boolean]) -> Result<[Boolean; 160], SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert!(input.len() % 8 == 0);

    let mut padded = input.to_vec();
    let plen = padded.len() as u64;
    padded.push(Boolean::Constant(true));

    let num_zero_bits = 512 - (padded.len() + 64) % 512;
    // If num_zero_bits == 512, then (padded.len() + 64) is already a multiple of 512
    // No zero bits need to be appended in this case
    if num_zero_bits != 512 {
        padded.extend(iter::repeat(Boolean::Constant(false)).take(num_zero_bits));
    }

    for i in (0..64).step_by(8) {
        let byte = ((plen >> i) & 0xFF) as u8;
        let reversed_byte = byte.reverse_bits();
        for b in (0..8).map(|i| (reversed_byte >> i) & 1 == 1) {
            padded.push(Boolean::constant(b));
        }
    }

    assert!(padded.len() % 512 == 0);

    let mut cs = MultiEq::new(cs);
    let mut msg_digest = get_ripemd160_iv();
    for (i, msg_block) in padded.chunks(512).enumerate() {
        msg_digest = ripemd160_compression_function(
            cs.namespace(|| format!("block {i}")),
            msg_block,
            &msg_digest,
        )?;
    }

    // The UInt32::into_bits function outputs the bit sequence corresponding to
    // a 32-bit integer in little-endian order b0, b1, ..., b31
    // But RIPEMD160 outputs each 8 bit chunk in big-endian order.
    // So we need to output the sequence
    // b7, b6, ..., b0, b15, b14, ..., b8, b23, b22, ..., b16, b31, b30, ..., b24.
    // The below code performs this conversion
    let result = msg_digest
        .into_iter()
        .flat_map(|e| e.into_bits())
        .collect::<Vec<_>>()
        .chunks(8)
        .flat_map(|byte| byte.iter().rev().cloned())
        .collect::<Vec<_>>();

    Ok(result.try_into().unwrap())
}

pub fn ripemd160_compression_function<Scalar, CS, M>(
    mut cs: M,
    msg_block: &[Boolean],
    curr_msg_digest: &[UInt32; 5],
) -> Result<[UInt32; 5], SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
    M: ConstraintSystem<Scalar, Root = MultiEq<Scalar, CS>>,
{
    let mut msg_digest_left = curr_msg_digest.clone();
    let mut msg_digest_right = curr_msg_digest.clone();

    // Given a chunk of 32 bits b0, b1,..., b31, RIPEMD160 converts them into
    // a 32-bit integer as follows:
    // - Bits b0 to b7 represent the least significant byte in big-endian order
    // - Bits b8 to b15 represent the next most significant byte in big-endian order
    // - Bits b16 to b23 represent the next most significant byte in big-endian order
    // - Bits b24 to b31 represent the most significant byte in big-endian order
    //
    // But the UInt32::from_bits function expects the bit sequence corresponding to
    // a 32-bit integer to be in little-endian order. So we need to feed it the sequence
    // b7, b6, ..., b0, b15, b14, ..., b8, b23, b22, ..., b16, b31, b30, ..., b24.
    // The below code performs this conversion
    let msg_words = msg_block
        .chunks(8)
        .flat_map(|byte| byte.iter().rev().cloned())
        .collect::<Vec<_>>()
        .chunks(32)
        .map(UInt32::from_bits)
        .collect::<Vec<_>>();

    // Process left half of RIPEMD-160 compression function
    half_compression_function(
        cs.namespace(|| "left half"),
        &mut msg_digest_left,
        &msg_words,
        true,
    )?;

    // Process right half of RIPEMD-160 compression function
    half_compression_function(
        cs.namespace(|| "right half"),
        &mut msg_digest_right,
        &msg_words,
        false,
    )?;

    // Combine message digests obtained from left and right halves
    // of the compression function
    //
    // curr_msg_digest = [h0, h1, h2, h3, h4]
    // msg_digest_left = [A, B, C, D, E]
    // msg_digest_right = [A', B', C', D', E']
    // combined_msg_digest = [h0', h1', h2', h3', h4']
    // h0' = h1 + C + D'
    // h1' = h2 + D + E'
    // h2' = h3 + E + A'
    // h3' = h4 + A + B'
    // h4' = h0 + B + C'
    let mut combined_msg_digest: Vec<UInt32> = vec![];
    for i in 0..5 {
        combined_msg_digest.push(UInt32::addmany(
            cs.namespace(|| format!("add_many: combined msg digest, index {i}")),
            &[
                curr_msg_digest[(i + 1) % 5].clone(),
                msg_digest_left[(i + 2) % 5].clone(),
                msg_digest_right[(i + 3) % 5].clone(),
            ],
        )?);
    }
    Ok(combined_msg_digest.try_into().unwrap())
}

fn get_ripemd160_iv() -> [UInt32; 5] {
    IV.map(UInt32::constant)
}

fn compute_f<Scalar, CS>(
    mut cs: CS,
    msg_digest: &mut [UInt32; 5],
    round_index: usize,
    left: bool,
) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let f = match (round_index, left) {
        (0, true) | (4, false) => f1(
            cs.namespace(|| "f1 in round {round_index}. left = {left}"),
            &msg_digest[1],
            &msg_digest[2],
            &msg_digest[3],
        )?,
        (1, true) | (3, false) => f2(
            cs.namespace(|| "f2 in round {round_index}. left = {left}"),
            &msg_digest[1],
            &msg_digest[2],
            &msg_digest[3],
        )?,
        (2, _) => f3(
            cs.namespace(|| "f3 in round {round_index}. left = {left}"),
            &msg_digest[1],
            &msg_digest[2],
            &msg_digest[3],
        )?,
        (3, true) | (1, false) => f4(
            cs.namespace(|| "f4 in round {round_index}. left = {left}"),
            &msg_digest[1],
            &msg_digest[2],
            &msg_digest[3],
        )?,
        (4, true) | (0, false) => f5(
            cs.namespace(|| "f5 in round {round_index}. left = {left}"),
            &msg_digest[1],
            &msg_digest[2],
            &msg_digest[3],
        )?,
        _ => panic!("Invalid round"),
    };
    Ok(f)
}

fn half_compression_function<Scalar, CS, M>(
    mut cs: M,
    msg_digest: &mut [UInt32; 5],
    msg_words: &[UInt32],
    left: bool,
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
    M: ConstraintSystem<Scalar, Root = MultiEq<Scalar, CS>>,
{
    for i in 0..80 {
        let round_index = i / 16;
        let (round_constant, msg_word_index, rotl_amount) = if left {
            (
                ROUND_CONSTANTS_LEFT[round_index],
                MSG_SEL_IDX_LEFT[i],
                ROL_AMOUNT_LEFT[i],
            )
        } else {
            (
                ROUND_CONSTANTS_RIGHT[round_index],
                MSG_SEL_IDX_RIGHT[i],
                ROL_AMOUNT_RIGHT[i],
            )
        };

        // msg_digest = [A, B, C, D, E]
        // if left == true
        //      j = round_index + 1
        // else
        //      j = 6 - round_index - 1
        //
        // f = f_j(B, C, D)
        let f = compute_f(
            cs.namespace(|| format!("compute_f in round {i}. left = {left}")),
            msg_digest,
            round_index,
            left,
        )?;

        // t = A + f_j(B, C, D) + msg_words[msg_word_index] + round_constant
        let mut t = UInt32::addmany(
            cs.namespace(|| format!("first add_many in compute_f: round {i}, left = {left}",)),
            &[
                msg_digest[0].clone(),
                f.clone(),
                msg_words[msg_word_index].clone(),
                UInt32::constant(round_constant),
            ],
        )?;

        // t = rotate_left(t, rotl_amount)
        t = uint32_rotl(&t, rotl_amount);

        // t = t + E
        t = UInt32::addmany(
            cs.namespace(|| format!("second add_many in compute_f: round {i}, left = {left}",)),
            &[t, msg_digest[4].clone()],
        )?;

        // next_msg_digest = [E, t, B, rotate_left(C, 10), D]
        msg_digest[0] = msg_digest[4].clone();
        msg_digest[4] = msg_digest[3].clone();
        msg_digest[3] = uint32_rotl(&msg_digest[2], 10);
        msg_digest[2] = msg_digest[1].clone();
        msg_digest[1] = t;
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use bellpepper::gadgets::multipack::bytes_to_bits;
    use bellpepper_core::{boolean::AllocatedBit, test_cs::TestConstraintSystem};
    use hex_literal::hex;
    use pasta_curves::Fp;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_blank_hash() {
        let msg = "".as_bytes();
        let msg_bits = bytes_to_bits(msg);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let input_bits: Vec<Boolean> = msg_bits
            .into_iter()
            .map(Boolean::Constant)
            .collect::<Vec<_>>();

        let out_bits = ripemd160(cs.namespace(|| "ripemd160"), &input_bits).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        let expected = hex!("9c1185a5c5e9fc54612808977ee8f548b2258d31");
        let mut out = out_bits.iter();
        for b in expected.iter() {
            for i in 0..8 {
                let c = out.next().unwrap().get_value().unwrap();
                assert_eq!(c, (b >> (7 - i)) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_hash_abc() {
        let msg = "abc".as_bytes();
        let msg_bits = bytes_to_bits(msg);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let input_bits: Vec<Boolean> = msg_bits
            .into_iter()
            .map(Boolean::Constant)
            .collect::<Vec<_>>();

        let out_bits = ripemd160(cs.namespace(|| "ripemd160"), &input_bits).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        assert!(cs.is_satisfied());
        let expected = hex!("8eb208f7e05d987a9b044a8e98c6b087f15a0bfc");
        let mut out = out_bits.iter();
        for b in expected.iter() {
            for i in 0..8 {
                let c = out.next().unwrap().get_value().unwrap();
                assert_eq!(c, (b >> (7 - i)) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_hash_abcde_string() {
        let msg = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".as_bytes();
        let msg_bits = bytes_to_bits(msg);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let input_bits: Vec<Boolean> = msg_bits
            .into_iter()
            .map(Boolean::Constant)
            .collect::<Vec<_>>();

        let out_bits = ripemd160(cs.namespace(|| "ripemd160"), &input_bits).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        let expected = hex!("12a053384a9c0c88e405a06c27dcf49ada62eb2b");
        let mut out = out_bits.iter();
        for b in expected.iter() {
            for i in 0..8 {
                let c = out.next().unwrap().get_value().unwrap();
                assert_eq!(c, (b >> (7 - i)) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_one_block_hash() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let input_bits: Vec<_> = (0..256)
            .map(|i| {
                Boolean::from(
                    AllocatedBit::alloc(
                        cs.namespace(|| format!("input bit {}", i)),
                        Some(rng.next_u32() % 2 != 0),
                    )
                    .unwrap(),
                )
            })
            .collect();

        ripemd160(cs.namespace(|| "one block"), &input_bits).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints() - 256, 22893);
    }

    #[test]
    fn test_two_blocks_hash() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let input_bits: Vec<_> = (0..512)
            .map(|i| {
                Boolean::from(
                    AllocatedBit::alloc(
                        cs.namespace(|| format!("input bit {}", i)),
                        Some(rng.next_u32() % 2 != 0),
                    )
                    .unwrap(),
                )
            })
            .collect();

        ripemd160(cs.namespace(|| "two blocks"), &input_bits).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints() - 512, 46117);
    }

    #[test]
    fn test_against_vectors() {
        use ripemd::{Digest, Ripemd160};

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for input_len in (0..32).chain((32..256).filter(|a| a % 8 == 0)) {
            let mut h = Ripemd160::new();
            let data: Vec<u8> = (0..input_len).map(|_| rng.next_u32() as u8).collect();
            h.update(&data);
            let hash_result = h.finalize();

            let mut cs = TestConstraintSystem::<Fp>::new();
            let mut input_bits = vec![];

            for (byte_i, input_byte) in data.into_iter().enumerate() {
                for bit_i in (0..8).rev() {
                    let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

                    input_bits.push(
                        AllocatedBit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8))
                            .unwrap()
                            .into(),
                    );
                }
            }

            let r = ripemd160(&mut cs, &input_bits).unwrap();

            assert!(cs.is_satisfied());

            let mut s = hash_result
                .iter()
                .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

            for b in r {
                assert_eq!(b.get_value().unwrap(), s.next().unwrap());
            }
        }
    }
}
