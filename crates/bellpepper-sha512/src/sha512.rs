//! Circuits for the [SHA-512] hash function and its internal compression
//! function.
//!
//! [SHA-512]: https://tools.ietf.org/html/rfc6234

// #![allow(clippy::many_single_char_names)]

use super::uint64::UInt64;
use bellpepper::gadgets::multieq::MultiEq;
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;

// Constants copied from https://github.com/RustCrypto/hashes/blob/master/sha2/src/consts.rs
#[allow(clippy::unreadable_literal)]
const ROUND_CONSTANTS: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

#[allow(clippy::unreadable_literal)]
const IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

pub fn sha512_block_no_padding<Scalar, CS>(
    mut cs: CS,
    input: &[Boolean],
) -> Result<Vec<Boolean>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), 1024);

    Ok(
        sha512_compression_function(&mut cs, input, &get_sha512_iv())?
            .into_iter()
            .flat_map(|e| e.into_bits_be())
            .collect(),
    )
}

pub fn sha512<Scalar, CS>(mut cs: CS, input: &[Boolean]) -> Result<Vec<Boolean>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert!(input.len() % 8 == 0);

    let mut padded = input.to_vec();
    let plen = padded.len() as u128;
    // append a single '1' bit
    padded.push(Boolean::constant(true));
    // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K + 128 is a multiple of 1024
    while (padded.len() + 128) % 1024 != 0 {
        padded.push(Boolean::constant(false));
    }
    // append L as a 128-bit big-endian integer, making the total post-processed length a multiple of 1024 bits
    for b in (0..128).rev().map(|i| (plen >> i) & 1 == 1) {
        padded.push(Boolean::constant(b));
    }
    assert!(padded.len() % 1024 == 0);

    let mut cur = get_sha512_iv();
    for (i, block) in padded.chunks(1024).enumerate() {
        cur = sha512_compression_function(cs.namespace(|| format!("block {}", i)), block, &cur)?;
    }

    Ok(cur.into_iter().flat_map(|e| e.into_bits_be()).collect())
}

fn get_sha512_iv() -> Vec<UInt64> {
    IV.iter().map(|&v| UInt64::constant(v)).collect()
}

pub fn sha512_compression_function<Scalar, CS>(
    cs: CS,
    input: &[Boolean],
    current_hash_value: &[UInt64],
) -> Result<Vec<UInt64>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), 1024);
    assert_eq!(current_hash_value.len(), 8);

    let mut w = input
        .chunks(64)
        .map(UInt64::from_bits_be)
        .collect::<Vec<_>>();

    // We can save some constraints by combining some of
    // the constraints in different u64 additions
    let mut cs = MultiEq::new(cs);

    for i in 16..80 {
        let cs = &mut cs.namespace(|| format!("w extension {}", i));

        // s0 := (w[i-15] rightrotate 1) xor (w[i-15] rightrotate 8) xor (w[i-15] rightshift 7)
        let mut s0 = w[i - 15].rotr(1);
        s0 = s0.xor(cs.namespace(|| "first xor for s0"), &w[i - 15].rotr(8))?;
        s0 = s0.xor(cs.namespace(|| "second xor for s0"), &w[i - 15].shr(7))?;

        // s1 := (w[i-2] rightrotate 19) xor (w[i-2] rightrotate 61) xor (w[i-2] rightshift 6)
        let mut s1 = w[i - 2].rotr(19);
        s1 = s1.xor(cs.namespace(|| "first xor for s1"), &w[i - 2].rotr(61))?;
        s1 = s1.xor(cs.namespace(|| "second xor for s1"), &w[i - 2].shr(6))?;

        let tmp = UInt64::addmany(
            cs.namespace(|| "computation of w[i]"),
            &[w[i - 16].clone(), s0, w[i - 7].clone(), s1],
        )?;

        // w[i] := w[i-16] + s0 + w[i-7] + s1
        w.push(tmp);
    }

    assert_eq!(w.len(), 80);

    enum Maybe {
        Deferred(Vec<UInt64>),
        Concrete(UInt64),
    }

    impl Maybe {
        fn compute<Scalar, CS, M>(self, cs: M, others: &[UInt64]) -> Result<UInt64, SynthesisError>
        where
            Scalar: PrimeField,
            CS: ConstraintSystem<Scalar>,
            M: ConstraintSystem<Scalar, Root = MultiEq<Scalar, CS>>,
        {
            Ok(match self {
                Maybe::Concrete(ref v) => return Ok(v.clone()),
                Maybe::Deferred(mut v) => {
                    v.extend(others.iter().cloned());
                    UInt64::addmany(cs, &v)?
                }
            })
        }
    }

    let mut a = Maybe::Concrete(current_hash_value[0].clone());
    let mut b = current_hash_value[1].clone();
    let mut c = current_hash_value[2].clone();
    let mut d = current_hash_value[3].clone();
    let mut e = Maybe::Concrete(current_hash_value[4].clone());
    let mut f = current_hash_value[5].clone();
    let mut g = current_hash_value[6].clone();
    let mut h = current_hash_value[7].clone();

    for i in 0..80 {
        let cs = &mut cs.namespace(|| format!("compression round {}", i));

        // S1 := (e rightrotate 14) xor (e rightrotate 18) xor (e rightrotate 41)
        let new_e = e.compute(cs.namespace(|| "deferred e computation"), &[])?;
        let mut s1 = new_e.rotr(14);
        s1 = s1.xor(cs.namespace(|| "first xor for s1"), &new_e.rotr(18))?;
        s1 = s1.xor(cs.namespace(|| "second xor for s1"), &new_e.rotr(41))?;

        // ch := (e and f) xor ((not e) and g)
        let ch = UInt64::sha512_ch(cs.namespace(|| "ch"), &new_e, &f, &g)?;

        // temp1 := h + S1 + ch + k[i] + w[i]
        let temp1 = vec![
            h.clone(),
            s1,
            ch,
            UInt64::constant(ROUND_CONSTANTS[i]),
            w[i].clone(),
        ];

        // S0 := (a rightrotate 28) xor (a rightrotate 34) xor (a rightrotate 39)
        let new_a = a.compute(cs.namespace(|| "deferred a computation"), &[])?;
        let mut s0 = new_a.rotr(28);
        s0 = s0.xor(cs.namespace(|| "first xor for s0"), &new_a.rotr(34))?;
        s0 = s0.xor(cs.namespace(|| "second xor for s0"), &new_a.rotr(39))?;

        // maj := (a and b) xor (a and c) xor (b and c)
        let maj = UInt64::sha512_maj(cs.namespace(|| "maj"), &new_a, &b, &c)?;

        // temp2 := S0 + maj
        let temp2 = vec![s0, maj];

        /*
        h := g
        g := f
        f := e
        e := d + temp1
        d := c
        c := b
        b := a
        a := temp1 + temp2
        */

        h = g;
        g = f;
        f = new_e;
        e = Maybe::Deferred(temp1.iter().cloned().chain(Some(d)).collect::<Vec<_>>());
        d = c;
        c = b;
        b = new_a;
        a = Maybe::Deferred(
            temp1
                .iter()
                .cloned()
                .chain(temp2.iter().cloned())
                .collect::<Vec<_>>(),
        );
    }

    /*
        Add the compressed chunk to the current hash value:
        h0 := h0 + a
        h1 := h1 + b
        h2 := h2 + c
        h3 := h3 + d
        h4 := h4 + e
        h5 := h5 + f
        h6 := h6 + g
        h7 := h7 + h
    */

    let h0 = a.compute(
        cs.namespace(|| "deferred h0 computation"),
        &[current_hash_value[0].clone()],
    )?;

    let h1 = UInt64::addmany(
        cs.namespace(|| "new h1"),
        &[current_hash_value[1].clone(), b],
    )?;

    let h2 = UInt64::addmany(
        cs.namespace(|| "new h2"),
        &[current_hash_value[2].clone(), c],
    )?;

    let h3 = UInt64::addmany(
        cs.namespace(|| "new h3"),
        &[current_hash_value[3].clone(), d],
    )?;

    let h4 = e.compute(
        cs.namespace(|| "deferred h4 computation"),
        &[current_hash_value[4].clone()],
    )?;

    let h5 = UInt64::addmany(
        cs.namespace(|| "new h5"),
        &[current_hash_value[5].clone(), f],
    )?;

    let h6 = UInt64::addmany(
        cs.namespace(|| "new h6"),
        &[current_hash_value[6].clone(), g],
    )?;

    let h7 = UInt64::addmany(
        cs.namespace(|| "new h7"),
        &[current_hash_value[7].clone(), h],
    )?;

    Ok(vec![h0, h1, h2, h3, h4, h5, h6, h7])
}

#[cfg(test)]
mod test {
    use super::*;
    use bellpepper_core::{boolean::AllocatedBit, test_cs::TestConstraintSystem};
    use blstrs::Scalar as Fr;
    use rand::Rng;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use sha2::{Digest, Sha512};

    #[test]
    #[allow(clippy::needless_collect)]
    fn test_hash() {
        let length: u8 = rand::thread_rng().gen();
        let mut h = Sha512::new();
        let data: Vec<u8> = (0..length).map(|_| rand::thread_rng().gen()).collect();
        h.update(&data);
        let hash_result = h.finalize();

        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut input_bits = vec![];

        for (byte_i, input_byte) in data.into_iter().enumerate() {
            for bit_i in (0..8).rev() {
                input_bits.push(
                    AllocatedBit::alloc(
                        cs.namespace(|| format!("input bit {} {}", byte_i, bit_i)),
                        Some((input_byte >> bit_i) & 1u8 == 1u8),
                    )
                    .unwrap()
                    .into(),
                );
            }
        }

        let r = sha512(&mut cs, &input_bits).unwrap();

        assert!(cs.is_satisfied());

        let s = hash_result
            .iter()
            .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

        for (i, j) in r.into_iter().zip(s) {
            assert_eq!(i.get_value(), Some(j));
        }
    }

    #[test]
    fn test_full_block() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let iv = get_sha512_iv();

        let mut cs = TestConstraintSystem::<Fr>::new();
        let input_bits: Vec<_> = (0..1024)
            .map(|i| {
                Boolean::from(
                    AllocatedBit::alloc(
                        cs.namespace(|| format!("input bit {}", i)),
                        Some(rng.next_u64() % 2 != 0),
                    )
                    .unwrap(),
                )
            })
            .collect();

        sha512_compression_function(cs.namespace(|| "sha512"), &input_bits, &iv).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(67123, cs.num_constraints());
    }

    #[test]
    fn test_full_hash() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fr>::new();
        let input_bits: Vec<_> = (0..1024)
            .map(|i| {
                Boolean::from(
                    AllocatedBit::alloc(
                        cs.namespace(|| format!("input bit {}", i)),
                        Some(rng.next_u64() % 2 != 0),
                    )
                    .unwrap(),
                )
            })
            .collect();

        sha512(cs.namespace(|| "sha512"), &input_bits).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(114129, cs.num_constraints());
    }

    #[test]
    fn test_against_vectors() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for input_len in (0..64).chain((64..512).filter(|a| a % 8 == 0)) {
            let mut h = Sha512::new();
            let data: Vec<u8> = (0..input_len).map(|_| rng.next_u64() as u8).collect();
            h.update(&data);
            let hash_result = h.finalize();

            let mut cs = TestConstraintSystem::<Fr>::new();
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

            let r = sha512(&mut cs, &input_bits).unwrap();

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
