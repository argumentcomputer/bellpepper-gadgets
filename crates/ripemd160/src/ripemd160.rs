//! Circuits for the [RIPEMD-160] hash function and its internal compression
//! function.
//!
//! [RIPEMD-160]: https://homes.esat.kuleuven.be/~bosselae/ripemd160.html

use bellpepper::gadgets::{multieq::MultiEq, uint32::UInt32};
use bellpepper_core::{boolean::Boolean, ConstraintSystem};
use ff::PrimeField;
use std::convert::TryInto;

use crate::util::{f1, f2, f3, f4, f5, swap_byte_endianness, uint32_rotl};

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

pub fn ripemd160<Scalar, CS>(
    cs: CS,
    input: &[Boolean],
) -> Result<[Boolean; 160], bellpepper_core::SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert!(input.len() % 8 == 0);

    let mut padded = input.to_vec();
    let plen = padded.len() as u64;
    padded.push(Boolean::Constant(true));

    while (padded.len() + 64) % 512 != 0 {
        padded.push(Boolean::constant(false));
    }

    for i in (0..64).step_by(8) {
        let byte = ((plen >> i) & 0xFF) as u8;
        let reversed_byte = byte.reverse_bits();
        for b in (0..8).map(|i| (reversed_byte >> i) & 1 == 1) {
            padded.push(Boolean::constant(b));
        }
    }

    assert!(padded.len() % 512 == 0);

    // Make the bytes little-endian
    let padded = swap_byte_endianness(&padded);

    let mut cur_md = get_ripemd160_iv();
    let mut cur_md_prime = cur_md.clone();
    let mut cs = MultiEq::new(cs);
    for (i, block) in padded.chunks(512).enumerate() {
        let prev_md = cur_md.clone();
        left_step(
            cs.namespace(|| format!("left_step {}", i)),
            block,
            &mut cur_md,
        );
        right_step(
            cs.namespace(|| format!("right_step {}", i)),
            block,
            &mut cur_md_prime,
        );
        cur_md = combine_left_and_right(
            cs.namespace(|| format!("combine_left_and_right_step {}", i)),
            cur_md,
            cur_md_prime,
            prev_md,
        )
        .unwrap();
        cur_md_prime = cur_md.clone();
    }
    let result = cur_md
        .into_iter()
        .flat_map(|e| e.into_bits())
        .collect::<Vec<_>>();

    // Make the bytes big-endian
    let result = swap_byte_endianness(&result);
    Ok(result.try_into().unwrap())
}

fn combine_left_and_right<Scalar, CS>(
    cs: CS,
    cur_md: [UInt32; 5],
    cur_md_prime: [UInt32; 5],
    prev_md: [UInt32; 5],
) -> Result<[UInt32; 5], bellpepper_core::SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let mut cs = MultiEq::new(cs);
    let mut update_md = cur_md.clone();
    for i in 0..5 {
        update_md[(i + 4) % 5] = UInt32::addmany(
            cs.namespace(|| format!("first add_many {}", i)),
            &[
                prev_md[i].clone(),
                cur_md[(i + 1) % 5].clone(),
                cur_md_prime[(i + 2) % 5].clone(),
            ],
        )
        .unwrap();
    }
    Ok(update_md)
}

fn get_ripemd160_iv() -> [UInt32; 5] {
    IV.map(UInt32::constant)
}

fn compute_f<Scalar, CS>(mut cs: CS, md_val: &mut [UInt32; 5], index: usize, left: bool) -> UInt32
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let f = match (index, left) {
        (0, true) | (4, false) => f1(
            cs.namespace(|| "f1 {index} {left}"),
            &md_val[1],
            &md_val[2],
            &md_val[3],
        )
        .unwrap(),
        (1, true) | (3, false) => f2(
            cs.namespace(|| "f2 {index} {left}"),
            &md_val[1],
            &md_val[2],
            &md_val[3],
        )
        .unwrap(),
        (2, _) => f3(
            cs.namespace(|| "f3 {index} {left}"),
            &md_val[1],
            &md_val[2],
            &md_val[3],
        )
        .unwrap(),
        (3, true) | (1, false) => f4(
            cs.namespace(|| "f4 {index} {left}"),
            &md_val[1],
            &md_val[2],
            &md_val[3],
        )
        .unwrap(),
        (4, true) | (0, false) => f5(
            cs.namespace(|| "f5 {index} {left}"),
            &md_val[1],
            &md_val[2],
            &md_val[3],
        )
        .unwrap(),
        _ => panic!("Invalid index"),
    };
    f
}

fn block<Scalar, CS>(cs: CS, md_val: &mut [UInt32; 5], w: Vec<UInt32>, left: bool)
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let mut cs = MultiEq::new(cs);
    let mut f: UInt32;
    let (k_val, i_val, s_val) = if left {
        (ROUND_CONSTANTS_LEFT, MSG_SEL_IDX_LEFT, ROL_AMOUNT_LEFT)
    } else {
        (ROUND_CONSTANTS_RIGHT, MSG_SEL_IDX_RIGHT, ROL_AMOUNT_RIGHT)
    };

    for i in 0..80 {
        let phase_index = i / 16;

        f = compute_f(
            cs.namespace(|| format!("Compute F block {} left {} index {}", phase_index, left, i)),
            md_val,
            phase_index,
            left,
        );
        let mut tmp1 = UInt32::addmany(
            cs.namespace(|| {
                format!(
                    "first add_many block {} left {} index {}",
                    phase_index, left, i
                )
            }),
            &[
                md_val[0].clone(),
                f.clone(),
                w[i_val[i]].clone(),
                UInt32::constant(k_val[phase_index]),
            ],
        )
        .unwrap();
        tmp1 = uint32_rotl(tmp1, s_val[i]);
        tmp1 = UInt32::addmany(
            cs.namespace(|| {
                format!(
                    "second add_many block {} left {} index {}",
                    phase_index, left, i
                )
            }),
            &[tmp1, md_val[4].clone()],
        )
        .unwrap();

        let tmp2 = uint32_rotl(md_val[2].clone(), 10);
        md_val[0] = md_val[4].clone();
        md_val[2] = md_val[1].clone();
        md_val[4] = md_val[3].clone();
        md_val[1] = tmp1.clone();
        md_val[3] = tmp2.clone();
    }
}

pub fn left_step<Scalar, CS>(cs: CS, input: &[Boolean], current_md_value: &mut [UInt32; 5])
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), 512);
    let w = input.chunks(32).map(UInt32::from_bits).collect::<Vec<_>>();
    let mut cs = MultiEq::new(cs);
    assert_eq!(w.len(), 16);
    block(
        cs.namespace(|| "block 0"),
        current_md_value,
        w.clone(),
        true,
    );
}

pub fn right_step<Scalar, CS>(cs: CS, input: &[Boolean], current_md_value: &mut [UInt32; 5])
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), 512);
    let w = input.chunks(32).map(UInt32::from_bits).collect::<Vec<_>>();
    let mut cs = MultiEq::new(cs);
    assert_eq!(w.len(), 16);
    block(
        cs.namespace(|| "block 0"),
        current_md_value,
        w.clone(),
        false,
    );
}

#[cfg(test)]
mod test {
    use super::*;
    use bellpepper::gadgets::multipack::bytes_to_bits;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use hex_literal::hex;
    use pasta_curves::Fp;

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
        let expected = hex!("12a053384a9c0c88e405a06c27dcf49ada62eb2b");
        let mut out = out_bits.iter();
        for b in expected.iter() {
            for i in 0..8 {
                let c = out.next().unwrap().get_value().unwrap();
                assert_eq!(c, (b >> (7 - i)) & 1u8 == 1u8);
            }
        }
    }
}
