//! Circuits for the [SHA-1] hash function and its internal compression
//! function.
//!
//! [SHA-1]: https://datatracker.ietf.org/doc/html/rfc3174

use bellpepper::gadgets::{multieq::MultiEq, uint32::UInt32};
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::util::{and_uint32, or_uint32};

const ROUND_CONSTANTS: [u32; 4] = [0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xca62c1d6];

const IV: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];

pub fn sha1_block_no_padding<Scalar, CS>(
    mut cs: CS,
    input: &[Boolean],
) -> Result<Vec<Boolean>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), 512);

    Ok(sha1_compression_function(&mut cs, input, &get_sha1_iv())?
        .into_iter()
        .flat_map(|e| e.into_bits_be())
        .collect())
}

pub fn sha1<Scalar, CS>(mut cs: CS, input: &[Boolean]) -> Result<Vec<Boolean>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert!(input.len() % 8 == 0);

    let mut padded = input.to_vec();
    let plen = padded.len() as u64;
    // append a single '1' bit
    padded.push(Boolean::constant(true));
    // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K + 64 is a multiple of 512
    while (padded.len() + 64) % 512 != 0 {
        padded.push(Boolean::constant(false));
    }
    // append L as a 64-bit big-endian integer, making the total post-processed length a multiple of 512 bits
    for b in (0..64).rev().map(|i| (plen >> i) & 1 == 1) {
        padded.push(Boolean::constant(b));
    }
    assert!(padded.len() % 512 == 0);

    let mut cur = get_sha1_iv();
    for (i, block) in padded.chunks(512).enumerate() {
        cur = sha1_compression_function(cs.namespace(|| format!("block {}", i)), block, &cur)?;
    }

    Ok(cur.into_iter().flat_map(|e| e.into_bits_be()).collect())
}

fn get_sha1_iv() -> Vec<UInt32> {
    IV.iter().map(|&v| UInt32::constant(v)).collect()
}

pub fn sha1_compression_function<Scalar, CS>(
    cs: CS,
    input: &[Boolean],
    current_hash_value: &[UInt32],
) -> Result<Vec<UInt32>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), 512);
    assert_eq!(current_hash_value.len(), 5);

    let mut w = input
        .chunks(32)
        .map(UInt32::from_bits_be)
        .collect::<Vec<_>>();

    // We can save some constraints by combining some of
    // the constraints in different u32 additions
    let mut cs = MultiEq::new(cs);

    for i in 16..80 {
        let cs = &mut cs.namespace(|| format!("w extension {}", i));

        // w[i] := (w[i-3] xor w[i-8] xor w[i-14] xor w[i-16]) leftrotate 1
        let mut wi = w[i - 3].xor(cs.namespace(|| format!("first xor for w[{i}]")), &w[i - 8])?;
        wi = wi.xor(
            cs.namespace(|| format!("second xor for w[{i}]")),
            &w[i - 14],
        )?;
        wi = wi.xor(cs.namespace(|| format!("third xor for w[{i}]")), &w[i - 16])?;

        // rotr(31) is equivalent to leftrotate 1
        wi = wi.rotr(31);
        w.push(wi);
    }

    assert_eq!(w.len(), 80);

    let mut a = current_hash_value[0].clone();
    let mut b = current_hash_value[1].clone();
    let mut c = current_hash_value[2].clone();
    let mut d = current_hash_value[3].clone();
    let mut e = current_hash_value[4].clone();

    for i in 0..80 {
        let cs = &mut cs.namespace(|| format!("compression round {}", i));

        let f = if i < 20 {
            // f = (b and c) or ((not b) and d)
            UInt32::sha256_ch(cs.namespace(|| "ch"), &b, &c, &d)?
        } else if !(40..60).contains(&i) {
            // b xor c xor d
            b.xor(cs.namespace(|| "b xor c"), &c)?
                .xor(cs.namespace(|| "b xor c xor d"), &d)?
        } else {
            let a1 = and_uint32(cs.namespace(|| "1st and"), &b, &c)?;
            let a2 = and_uint32(cs.namespace(|| "2nd and"), &b, &d)?;
            let a3 = and_uint32(cs.namespace(|| "3rd and"), &c, &d)?;

            let tmp = or_uint32(cs.namespace(|| "1st or"), &a1, &a2)?;
            or_uint32(cs.namespace(|| "2nd or"), &tmp, &a3)?
        };

        // temp = (a leftrotate 5) + f + e + k + w[i]
        let temp = UInt32::addmany(
            cs.namespace(|| "temp"),
            &[
                a.rotr(27),
                f,
                e,
                UInt32::constant(ROUND_CONSTANTS[i / 20]),
                w[i].clone(),
            ],
        )?;

        /*
        e = d
        d = c
        c = b leftrotate 30
        b = a
        a = temp
        */

        e = d;
        d = c;
        c = b.rotr(2);
        b = a;
        a = temp;
    }

    /*
        Add the compressed chunk to the current hash value:
        h0 := h0 + a
        h1 := h1 + b
        h2 := h2 + c
        h3 := h3 + d
        h4 := h4 + e
    */

    let h0 = UInt32::addmany(
        cs.namespace(|| "new h0"),
        &[current_hash_value[0].clone(), a],
    )?;

    let h1 = UInt32::addmany(
        cs.namespace(|| "new h1"),
        &[current_hash_value[1].clone(), b],
    )?;

    let h2 = UInt32::addmany(
        cs.namespace(|| "new h2"),
        &[current_hash_value[2].clone(), c],
    )?;

    let h3 = UInt32::addmany(
        cs.namespace(|| "new h3"),
        &[current_hash_value[3].clone(), d],
    )?;

    let h4 = UInt32::addmany(
        cs.namespace(|| "new h4"),
        &[current_hash_value[4].clone(), e],
    )?;

    Ok(vec![h0, h1, h2, h3, h4])
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
        let iv = get_sha1_iv();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut input_bits: Vec<_> = (0..512).map(|_| Boolean::Constant(false)).collect();
        input_bits[0] = Boolean::Constant(true);
        let out = sha1_compression_function(&mut cs, &input_bits, &iv).unwrap();
        let out_bits = out.into_iter().flat_map(|e| e.into_bits_be());

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        let expected = hex!("da39a3ee5e6b4b0d3255bfef95601890afd80709");

        let mut out = out_bits;
        for b in expected.iter() {
            for i in (0..8).rev() {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_hash_abc() {
        let iv = get_sha1_iv();

        let msg = "abc".as_bytes();
        let msg_bits = bytes_to_bits(msg);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut input_bits = msg_bits
            .into_iter()
            .map(Boolean::Constant)
            .collect::<Vec<_>>();
        input_bits.push(Boolean::Constant(true));
        input_bits.append(&mut vec![Boolean::Constant(false); 479]);
        // The number 24 as a boolean vector
        let mut len = vec![false, false, false, true, true, false, false, false]
            .into_iter()
            .map(Boolean::Constant)
            .collect::<Vec<_>>();
        input_bits.append(&mut len);

        let out = sha1_compression_function(&mut cs, &input_bits, &iv).unwrap();
        let out_bits = out.into_iter().flat_map(|e| e.into_bits_be());

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        let expected = hex!("a9993e364706816aba3e25717850c26c9cd0d89d");

        let mut out = out_bits;
        for b in expected.iter() {
            for i in (0..8).rev() {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
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
            .enumerate()
            .map(|(i, b)| {
                Boolean::from(
                    AllocatedBit::alloc(cs.namespace(|| format!("input bit {}", i)), Some(b))
                        .unwrap(),
                )
            })
            .collect();

        let out_bits = sha1(cs.namespace(|| "sha1"), &input_bits).unwrap();
        assert!(cs.is_satisfied());

        let expected = hex!("84983e441c3bd26ebaae4aa1f95129e5e54670f1");
        let mut out = out_bits.iter();
        for b in expected.iter() {
            for i in (0..8).rev() {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_full_block() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let iv = get_sha1_iv();

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

        sha1_compression_function(cs.namespace(|| "sha1"), &input_bits, &iv).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints() - 512, 16706);
    }

    #[test]
    fn test_full_hash() {
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

        sha1(cs.namespace(|| "sha1"), &input_bits).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints() - 512, 27364);
    }

    #[test]
    fn test_against_vectors() {
        use sha1::{Digest, Sha1};

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for input_len in (0..32).chain((32..256).filter(|a| a % 8 == 0)) {
            let mut h = Sha1::new();
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

            let r = sha1(&mut cs, &input_bits).unwrap();

            assert!(cs.is_satisfied());

            let mut s = hash_result
                .iter()
                .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

            for b in r {
                match b {
                    Boolean::Is(b) => {
                        assert!(s.next().unwrap() == b.get_value().unwrap());
                    }
                    Boolean::Not(b) => {
                        assert!(s.next().unwrap() != b.get_value().unwrap());
                    }
                    Boolean::Constant(b) => {
                        assert!(input_len == 0);
                        assert!(s.next().unwrap() == b);
                    }
                }
            }
        }
    }
}
