//! Circuits for the [RIPEMD-160] hash function and its internal compression
//! function.
//!
//! [RIPEMD-160]: https://www.esat.kuleuven.be/cosic/publications/article-317.pdf

use bellpepper::gadgets::{multieq::MultiEq, uint32::UInt32};
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::util::{ripemd_d1, ripemd_d2, shl_uint32};

#[allow(clippy::unreadable_literal)]
const MD_BUFFERS: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];

#[allow(clippy::unreadable_literal)]
const MD_BUFFERS_PRIME: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];

#[allow(clippy::unreadable_literal)]
const K_BUFFER: [u32; 5] = [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e];

#[allow(clippy::unreadable_literal)]
const K_BUFFER_PRIME: [u32; 5] = [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000];

pub fn ripemd160<Scalar, CS>(
    mut cs: CS,
    input: &[Boolean],
) -> Result<Vec<Boolean>, bellpepper_core::SynthesisError>
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
    for b in (0..64).rev().map(|i| (plen >> i) & 1 == 1) {
        padded.push(Boolean::constant(b));
    }
    assert!(padded.len() % 512 == 0);
    let mut cur_md = get_ripemd160_md("md");
    let mut cur_md_prime = get_ripemd160_md("md_prime");
    for (i, block) in padded.chunks(512).enumerate() {
        let prev_md = cur_md.clone();
        cur_md = ripemd160_func_block(cs.namespace(|| format!("block {}", i)), block, &mut cur_md)?;
        cur_md_prime = ripemd160_func_block_prime(
            cs.namespace(|| format!("block_prime {}", i)),
            block,
            &mut cur_md_prime,
        )?;
        let mut update_md = cur_md.clone();
        for i in 0..5 {
            update_md[(i + 4) % 5] = prev_md[i].xor(
                cs.namespace(|| format!("first xor {}", i)),
                &cur_md[(i + 1) % 5],
            )?;
            update_md[(i + 4) % 5] = update_md[(i + 4) % 5].xor(
                cs.namespace(|| format!("second xor {}", i)),
                &cur_md_prime[(i + 2) % 5],
            )?;
        }
        cur_md = update_md;
        cur_md_prime = cur_md.clone();
    }
    Ok(cur_md.into_iter().flat_map(|e| e.into_bits_be()).collect())
}

fn get_ripemd160_md(input: &str) -> Vec<UInt32> {
    match input {
        "md" => MD_BUFFERS.iter().map(|&v| UInt32::constant(v)).collect(),
        "md_prime" => MD_BUFFERS_PRIME
            .iter()
            .map(|&v| UInt32::constant(v))
            .collect(),
        _ => panic!("Invalid input"),
    }
}

pub fn ripemd160_func_block<Scalar, CS>(
    cs: CS,
    input: &[Boolean],
    current_md_value: &mut [UInt32],
) -> Result<Vec<UInt32>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), 512);
    assert_eq!(current_md_value.len(), 5);
    let w = input
        .chunks(32)
        .map(UInt32::from_bits_be)
        .collect::<Vec<_>>();
    let mut cs = MultiEq::new(cs);
    let mut f = current_md_value[1]
        .xor(cs.namespace(|| "first xor"), &current_md_value[2])?
        .xor(cs.namespace(|| "second xor"), &current_md_value[3])?;
    let mut s_val = [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER[0]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    f = UInt32::ripemd_d1(
        cs.namespace(|| "d1"),
        &current_md_value[3],
        &current_md_value[1],
        &current_md_value[2],
    )?;
    s_val = [7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12];
    let mut i_val = [7, 14, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER[1]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    f = UInt32::ripemd_d2(
        cs.namespace(|| "d2"),
        &current_md_value[3],
        &current_md_value[1],
        &current_md_value[2],
    )?;
    s_val = [11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5];
    i_val = [3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER[2]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    f = UInt32::ripemd_d1(
        cs.namespace(|| "d1"),
        &current_md_value[1],
        &current_md_value[3],
        &current_md_value[2],
    )?;
    s_val = [11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12];
    i_val = [1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER[3]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    f = UInt32::ripemd_d2(
        cs.namespace(|| "d2"),
        &current_md_value[1],
        &current_md_value[2],
        &current_md_value[3],
    )?;
    s_val = [9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6];
    i_val = [4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER[3]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    Ok(vec![
        current_md_value[0].clone(),
        current_md_value[1].clone(),
        current_md_value[2].clone(),
        current_md_value[3].clone(),
        current_md_value[4].clone(),
    ])
}

pub fn ripemd160_func_block_prime<Scalar, CS>(
    cs: CS,
    input: &[Boolean],
    current_md_value: &mut [UInt32],
) -> Result<Vec<UInt32>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), 512);
    assert_eq!(current_md_value.len(), 5);
    let mut w = input
        .chunks(32)
        .map(UInt32::from_bits_be)
        .collect::<Vec<_>>();
    let mut cs = MultiEq::new(cs);
    let mut f = UInt32::ripemd_d2(
        cs.namespace(|| "d2"),
        &current_md_value[1],
        &current_md_value[2],
        &current_md_value[3],
    )?;
    let mut s_val = [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6];
    let mut i_val = [5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER_PRIME[0]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    f = UInt32::ripemd_d1(
        cs.namespace(|| "d1"),
        &current_md_value[1],
        &current_md_value[3],
        &current_md_value[2],
    )?;
    s_val = [9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11];
    i_val = [6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER_PRIME[1]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    f = UInt32::ripemd_d2(
        cs.namespace(|| "d2"),
        &current_md_value[3],
        &current_md_value[1],
        &current_md_value[2],
    )?;
    s_val = [9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5];
    i_val = [15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER_PRIME[2]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    f = UInt32::ripemd_d1(
        cs.namespace(|| "d1"),
        &current_md_value[2],
        &current_md_value[1],
        &current_md_value[3],
    )?;
    s_val = [15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8];
    i_val = [8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER_PRIME[3]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    f = current_md_value[1]
        .xor(cs.namespace(|| "first xor"), &current_md_value[2])?
        .xor(cs.namespace(|| "second xor"), &current_md_value[3])?;
    s_val = [8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11];
    i_val = [12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11];
    for i in 0..16 {
        let mut tmp1 = current_md_value[0]
            .xor(cs.namespace(|| format!("first xor {}", i)), &f)?
            .xor(cs.namespace(|| format!("second xor {}", i)), &w[i_val[i]])?
            .xor(
                cs.namespace(|| format!("third xor {}", i)),
                &UInt32::constant(K_BUFFER_PRIME[4]),
            )?;
        tmp1 = current_md_value[0].shl(s_val[i]);
        tmp1 = current_md_value[0].xor(
            cs.namespace(|| format!("fourth xor {}", i)),
            &current_md_value[4],
        )?;
        let tmp2 = current_md_value[2].shl(10);
        current_md_value[0] = current_md_value[4].clone();
        current_md_value[2] = current_md_value[1].clone();
        current_md_value[4] = current_md_value[3].clone();
        current_md_value[1] = tmp1.clone();
        current_md_value[3] = tmp2.clone();
    }
    Ok(vec![
        current_md_value[0].clone(),
        current_md_value[1].clone(),
        current_md_value[2].clone(),
        current_md_value[3].clone(),
        current_md_value[4].clone(),
    ])
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::gadgets::boolean::AllocatedBit;
    use bellpepper_core::test_cs::*;
    use blstrs::Scalar as Fr;
    use hex_literal::hex;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    #[test]
    #[allow(clippy::needless_collect)]
    fn test_blank_hash() {
        let mut cur_md = get_ripemd160_md("md");
        let mut cur_md_prime = get_ripemd160_md("md_prime");

        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut input_bits: Vec<_> = (0..512).map(|_| Boolean::Constant(false)).collect();
        input_bits[0] = Boolean::Constant(true);
        let prev_md = cur_md.clone();
        cur_md = ripemd160_func_block(&mut cs, &input_bits, &mut cur_md).unwrap();
        cur_md_prime = ripemd160_func_block_prime(&mut cs, &input_bits, &mut cur_md_prime).unwrap();
        let mut update_md = cur_md.clone();
        for i in 0..5 {
            match prev_md[i].xor(
                cs.namespace(|| format!("first xor {}", i)),
                &cur_md[(i + 1) % 5],
            ) {
                Ok(result) => {
                    update_md[(i + 4) % 5] = result;
                }
                Err(err) => {
                    // Handle the error here
                }
            }
            match update_md[(i + 4) % 5].xor(
                cs.namespace(|| format!("first xor {}", i)),
                &cur_md[(i + 2) % 5],
            ) {
                Ok(result) => {
                    update_md[(i + 4) % 5] = result;
                }
                Err(err) => {
                    // Handle the error here
                }
            }
        }
        cur_md = update_md;
        cur_md_prime = cur_md.clone();
        // let out_bits : Vec<_> = cur_md.into_iter().flat_map(|e| e.into_bits_be()).collect();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        // let expected = hex!("9c1185a5c5e9fc54612808977ee8f548b2258d31");

        // let out = out_bits;
        // for b in expected.iter() {
        //     for i in (0..8).rev() {
        //         let c = out.next().unwrap().get_value().unwrap();

        //         assert_eq!(c, (b >> i) & 1u8 == 1u8);
        //     }
        // }
    }
}
