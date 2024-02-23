//! Circuit representation of a [`u64`],
//!
// TODO: consider upstreaming to Bellpepper

use bellpepper::gadgets::multieq::MultiEq;
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use core::fmt;
use ff::PrimeField;

/// Represents an interpretation of 64 `Boolean` objects as an
/// unsigned integer.
#[derive(Clone)]
pub struct UInt64 {
    // Least significant bit first
    bits: Vec<Boolean>,
    value: Option<u64>,
}

impl UInt64 {
    /// Construct a constant `UInt64` from a `u64`
    pub fn constant(value: u64) -> Self {
        let mut bits = Vec::with_capacity(64);

        let mut tmp = value;
        for _ in 0..64 {
            if tmp & 1 == 1 {
                bits.push(Boolean::constant(true))
            } else {
                bits.push(Boolean::constant(false))
            }

            tmp >>= 1;
        }

        Self {
            bits,
            value: Some(value),
        }
    }

    /// Allocate a `UInt64` in the constraint system
    #[allow(dead_code)]
    pub fn alloc<E, CS>(mut cs: CS, value: Option<u64>) -> Result<Self, SynthesisError>
    where
        E: PrimeField,
        CS: ConstraintSystem<E>,
    {
        let values = match value {
            Some(mut val) => {
                let mut v = Vec::with_capacity(64);

                for _ in 0..64 {
                    v.push(Some(val & 1 == 1));
                    val >>= 1;
                }

                v
            }
            None => vec![None; 64],
        };

        let bits = values
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("allocated bit {}", i)),
                    v,
                )?))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(Self { bits, value })
    }

    pub fn into_bits_be(self) -> Vec<Boolean> {
        let mut ret = self.bits;
        ret.reverse();
        ret
    }

    pub fn from_bits_be(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 64);

        let mut value = Some(0u64);
        for b in bits {
            if let Some(v) = value.as_mut() {
                *v <<= 1;
            }

            match b.get_value() {
                Some(true) => {
                    if let Some(v) = value.as_mut() {
                        *v |= 1;
                    }
                }
                Some(false) => {}
                None => {
                    value = None;
                }
            }
        }

        Self {
            value,
            bits: bits.iter().rev().cloned().collect(),
        }
    }

    /// Turns this `UInt64` into its little-endian byte order representation.
    pub fn into_bits(self) -> Vec<Boolean> {
        self.bits
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `UInt64`.
    pub fn from_bits(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 64);

        let new_bits = bits.to_vec();

        let mut value = Some(0u64);
        for b in new_bits.iter().rev() {
            if let Some(v) = value.as_mut() {
                *v <<= 1;
            }

            match *b {
                Boolean::Constant(b) => {
                    if b {
                        if let Some(v) = value.as_mut() {
                            *v |= 1;
                        }
                    }
                }
                Boolean::Is(ref b) => match b.get_value() {
                    Some(true) => {
                        if let Some(v) = value.as_mut() {
                            *v |= 1;
                        }
                    }
                    Some(false) => {}
                    None => value = None,
                },
                Boolean::Not(ref b) => match b.get_value() {
                    Some(false) => {
                        if let Some(v) = value.as_mut() {
                            *v |= 1;
                        }
                    }
                    Some(true) => {}
                    None => value = None,
                },
            }
        }

        Self {
            value,
            bits: new_bits,
        }
    }

    #[allow(dead_code)]
    pub fn rotr(&self, by: usize) -> Self {
        let by = by % 64;

        let new_bits = self
            .bits
            .iter()
            .skip(by)
            .chain(self.bits.iter())
            .take(64)
            .cloned()
            .collect();

        Self {
            bits: new_bits,
            value: self.value.map(|v| v.rotate_right(by as u32)),
        }
    }

    pub fn rotl(&self, by: usize) -> Self {
        //ROTL = 64 - ROTR
        let by = (64 - by) % 64;

        let new_bits = self
            .bits
            .iter()
            .skip(by)
            .chain(self.bits.iter())
            .take(64)
            .cloned()
            .collect();

        Self {
            bits: new_bits,
            value: self.value.map(|v| v.rotate_right(by as u32)),
        }
    }

    /// XOR this `UInt64` with another `UInt64`
    pub fn xor<E, CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        E: PrimeField,
        CS: ConstraintSystem<E>,
    {
        let new_value = match (self.value, other.value) {
            (Some(a), Some(b)) => Some(a ^ b),
            _ => None,
        };

        let bits = self
            .bits
            .iter()
            .zip(other.bits.iter())
            .enumerate()
            .map(|(i, (a, b))| Boolean::xor(cs.namespace(|| format!("xor of bit {}", i)), a, b))
            .collect::<Result<_, _>>()?;

        Ok(Self {
            bits,
            value: new_value,
        })
    }

    /// AND this `UInt64` with another `UInt64`
    pub fn and<E, CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        E: PrimeField,
        CS: ConstraintSystem<E>,
    {
        let new_value = match (self.value, other.value) {
            (Some(a), Some(b)) => Some(a & b),
            _ => None,
        };

        let bits = self
            .bits
            .iter()
            .zip(other.bits.iter())
            .enumerate()
            .map(|(i, (a, b))| Boolean::and(cs.namespace(|| format!("and of bit {}", i)), a, b))
            .collect::<Result<_, _>>()?;

        Ok(Self {
            bits,
            value: new_value,
        })
    }

    /// NOT this `UInt64`
    pub fn not(&self) -> Self {
        let new_value = self.value.map(|a| !a);

        let bits = self.bits.iter().map(|a| a.not()).collect();

        Self {
            bits,
            value: new_value,
        }
    }

    pub fn shr(&self, by: usize) -> Self {
        let by = by % 64;

        let fill = Boolean::constant(false);

        let new_bits = self
            .bits
            .iter() // The bits are least significant first
            .skip(by) // Skip the bits that will be lost during the shift
            .chain(Some(&fill).into_iter().cycle()) // Rest will be zeros
            .take(64) // Only 64 bits needed!
            .cloned()
            .collect();

        Self {
            bits: new_bits,
            value: self.value.map(|v| v >> by as u32),
        }
    }

    /// Perform modular addition of several `UInt64` objects.
    /// # Panics
    ///
    /// This function will panic if Scalar::NUM_BITS < 64 or number of operands are less than 2 or number of operands are greater than 10
    ///  
    pub fn addmany<Scalar, CS, M>(mut cs: M, operands: &[Self]) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
        M: ConstraintSystem<Scalar, Root = MultiEq<Scalar, CS>>,
    {
        // Make some arbitrary bounds for ourselves to avoid overflows
        // in the scalar field
        assert!(Scalar::NUM_BITS >= 64, "Assertion failed: Number of bits required to represent a field element should not be less than 64");
        assert!(
            operands.len() >= 2,
            "Assertion failed: Operands length should not be less than 2"
        ); // Weird trivial cases that should never happen
        assert!(
            operands.len() <= 10,
            "Assertion failed: Operands length should not be greater than 10"
        );

        // Compute the maximum value of the sum so we allocate enough bits for
        // the result
        let mut max_value = (operands.len() as u128) * (u128::from(u64::max_value()));

        // Keep track of the resulting value
        let mut result_value = Some(0u128);

        // This is a linear combination that we will enforce to equal the
        // output
        let mut lc = LinearCombination::zero();

        let mut all_constants = true;

        // Iterate over the operands
        for op in operands {
            // Accumulate the value
            match op.value {
                Some(val) => {
                    if let Some(v) = result_value.as_mut() {
                        *v += u128::from(val);
                    }
                }
                None => {
                    // If any of our operands have unknown value, we won't
                    // know the value of the result
                    result_value = None;
                }
            }

            // Iterate over each bit of the operand and add the operand to
            // the linear combination
            let mut coeff = Scalar::ONE;
            for bit in &op.bits {
                lc = lc + &bit.lc(CS::one(), coeff);

                all_constants &= bit.is_constant();

                coeff = coeff.double();
            }
        }

        // The value of the actual result is modulo 2^64
        let modular_value = result_value.map(|v| v as u64);

        if all_constants && modular_value.is_some() {
            // We can just return a constant, rather than
            // unpacking the result into allocated bits.

            if let Some(mv) = modular_value {
                return Ok(Self::constant(mv));
            }
        }

        // Storage area for the resulting bits
        let mut result_bits = vec![];

        // Linear combination representing the output,
        // for comparison with the sum of the operands
        let mut result_lc = LinearCombination::zero();

        // Allocate each bit of the result
        let mut coeff = Scalar::ONE;
        let mut i = 0;
        while max_value != 0 {
            // Allocate the bit
            let b = AllocatedBit::alloc(
                cs.namespace(|| format!("result bit {}", i)),
                result_value.map(|v| (v >> i) & 1 == 1),
            )?;

            // Add this bit to the result combination
            result_lc = result_lc + (coeff, b.get_variable());

            result_bits.push(b.into());

            max_value >>= 1;
            i += 1;
            coeff = coeff.double();
        }

        // Enforce equality between the sum and result
        cs.get_root().enforce_equal(i, &lc, &result_lc);

        // Discard carry bits that we don't care about
        result_bits.truncate(64);

        Ok(Self {
            bits: result_bits,
            value: modular_value,
        })
    }

    fn triop<Scalar, CS, F, U>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        c: &Self,
        tri_fn: F,
        circuit_fn: U,
    ) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
        F: Fn(u64, u64, u64) -> u64,
        U: Fn(&mut CS, usize, &Boolean, &Boolean, &Boolean) -> Result<Boolean, SynthesisError>,
    {
        let new_value = match (a.value, b.value, c.value) {
            (Some(a), Some(b), Some(c)) => Some(tri_fn(a, b, c)),
            _ => None,
        };

        let bits = a
            .bits
            .iter()
            .zip(b.bits.iter())
            .zip(c.bits.iter())
            .enumerate()
            .map(|(i, ((a, b), c))| circuit_fn(&mut cs, i, a, b, c))
            .collect::<Result<_, _>>()?;

        Ok(Self {
            bits,
            value: new_value,
        })
    }

    /// Compute the `maj` value (a and b) xor (a and c) xor (b and c)
    /// during SHA512.
    pub fn sha512_maj<Scalar, CS>(
        cs: CS,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        Self::triop(
            cs,
            a,
            b,
            c,
            |a, b, c| (a & b) ^ (a & c) ^ (b & c),
            // Boolean::sha256_maj operates on 3 Booleans and outputs the majority Boolean.
            // It will remain same for sha512_maj since it does not take into account UInt32 or UInt64.
            |cs, i, a, b, c| Boolean::sha256_maj(cs.namespace(|| format!("maj {}", i)), a, b, c),
        )
    }

    /// Compute the `ch` value `(a and b) xor ((not a) and c)`
    /// during SHA512.
    pub fn sha512_ch<Scalar, CS>(
        cs: CS,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        Self::triop(
            cs,
            a,
            b,
            c,
            |a, b, c| (a & b) ^ ((!a) & c),
            // Boolean::sha256_ch operates on 3 Booleans and outputs the choice Boolean.
            // It will remain same for sha512_ch since it does not take into account UInt32 or UInt64.
            |cs, i, a, b, c| Boolean::sha256_ch(cs.namespace(|| format!("ch {}", i)), a, b, c),
        )
    }
}

impl fmt::Display for UInt64 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tmp = format!("{:#x}", self.value.unwrap());

        formatter.pad_integral(true, "UInt64 ", &tmp)
    }
}

impl fmt::Debug for UInt64 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tmp = format!("{:#x}", self.value.unwrap());

        formatter.pad_integral(true, "UInt64 ", &tmp)
    }
}

#[cfg(test)]
mod test {
    use super::UInt64;
    use bellpepper::gadgets::multieq::MultiEq;
    use bellpepper_core::boolean::Boolean;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bellpepper_core::ConstraintSystem;

    use bitvec::prelude::*;
    use blstrs::Scalar as Fr;
    use ff::Field;
    use proptest::prelude::*;
    use rand_core::SeedableRng as _;
    use rand_xorshift::XorShiftRng;
    use std::convert::TryInto;

    proptest! {
        #[test]
        fn test_uint64_from_constant(a: u64) {
            let b = UInt64::constant(a);
            assert_eq!(a, b.value.unwrap());
        }

        #[test]
        fn test_uint64_from_bits_be(a: u64) {
            let a_bv = BitVec::<u64, Msb0>::from_element(a);
            let a_bits: Vec<Boolean> = a_bv.iter().map(|b| Boolean::constant(*b)).collect();
            let b = UInt64::from_bits_be(&a_bits);
            assert_eq!(a, b.value.unwrap());
        }

        #[test]
        fn test_uint64_from_bits(a: u64) {
            let a_bv = BitVec::<u64, Lsb0>::from_element(a);
            let a_bits: Vec<Boolean> = a_bv.iter().map(|b| Boolean::constant(*b)).collect();
            let b = UInt64::from_bits(&a_bits);
            assert_eq!(a, b.value.unwrap());
        }

        #[test]
        fn test_uint64_xor(a: u64, b: u64, c: u64) {
            let mut cs = TestConstraintSystem::<pasta_curves::pallas::Scalar>::new();

            let expected = a ^ b ^ c;

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b); // Just to mix things up
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = a_bit.xor(cs.namespace(|| "first xor"), &b_bit).unwrap();
            let r = r.xor(cs.namespace(|| "second xor"), &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(r.value.unwrap(), expected);
        }

        #[test]
        fn test_uint64_rotr(a: u64) {
            let num = UInt64::constant(a);

            for i in 0..64 {
                let b = num.rotr(i);
                assert_eq!(b.value.unwrap(), a.rotate_right(i.try_into().unwrap()));
            }
        }

    }

    #[test]
    fn test_uint64_addmany_constants() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = rng.next_u64();
            let b = rng.next_u64();
            let c = rng.next_u64();

            let a_bit = UInt64::constant(a);
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::constant(c);

            let mut expected = a.wrapping_add(b).wrapping_add(c);

            let r = {
                let mut cs = MultiEq::new(&mut cs);
                let r =
                    UInt64::addmany(cs.namespace(|| "addition"), &[a_bit, b_bit, c_bit]).unwrap();
                r
            };

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match *b {
                    Boolean::Is(_) | Boolean::Not(_) => panic!(),
                    Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn test_uint64_addmany() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = rng.next_u64();
            let b = rng.next_u64();
            let c = rng.next_u64();
            let d = rng.next_u64();

            let mut expected = (a ^ b).wrapping_add(c).wrapping_add(d);

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::constant(c);
            let d_bit = UInt64::alloc(cs.namespace(|| "d_bit"), Some(d)).unwrap();

            let r = a_bit.xor(cs.namespace(|| "xor"), &b_bit).unwrap();
            let r = {
                let mut cs = MultiEq::new(&mut cs);
                UInt64::addmany(cs.namespace(|| "addition"), &[r, c_bit, d_bit]).unwrap()
            };

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match *b {
                    Boolean::Is(ref b) => {
                        assert_eq!(b.get_value().unwrap(), expected & 1 == 1);
                    }
                    Boolean::Not(ref b) => {
                        assert_ne!(b.get_value().unwrap(), expected & 1 == 1);
                    }
                    Boolean::Constant(_) => unreachable!(),
                }

                expected >>= 1;
            }

            // Flip a bit and see if the addition constraint still works
            if cs.get("addition/result bit 0/boolean").is_zero().into() {
                cs.set("addition/result bit 0/boolean", Field::ONE);
            } else {
                cs.set("addition/result bit 0/boolean", Field::ZERO);
            }

            assert!(!cs.is_satisfied());
        }
    }

    #[test]
    fn test_uint64_shr() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..50 {
            for i in 0..120 {
                let num = rng.next_u64();
                let a = UInt64::constant(num).shr(i);
                let b = UInt64::constant(num.wrapping_shr(i as u32));

                assert_eq!(a.value.unwrap(), b.value.unwrap());

                assert_eq!(a.bits.len(), b.bits.len());
                for (a, b) in a.bits.iter().zip(b.bits.iter()) {
                    assert_eq!(a.get_value().unwrap(), b.get_value().unwrap());
                }
            }
        }
    }

    #[test]
    fn test_uint64_sha512_maj() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = rng.next_u64();
            let b = rng.next_u64();
            let c = rng.next_u64();

            let mut expected = (a & b) ^ (a & c) ^ (b & c);

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = UInt64::sha512_maj(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match *b {
                    Boolean::Is(ref b) => {
                        assert_eq!(b.get_value().unwrap(), expected & 1 == 1);
                    }
                    Boolean::Not(ref b) => {
                        assert_ne!(b.get_value().unwrap(), expected & 1 == 1);
                    }
                    Boolean::Constant(b) => {
                        assert_eq!(b, expected & 1 == 1);
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    fn test_uint64_sha512_ch() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = rng.next_u64();
            let b = rng.next_u64();
            let c = rng.next_u64();

            let mut expected = (a & b) ^ ((!a) & c);

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = UInt64::sha512_ch(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match *b {
                    Boolean::Is(ref b) => {
                        assert_eq!(b.get_value().unwrap(), expected & 1 == 1);
                    }
                    Boolean::Not(ref b) => {
                        assert_ne!(b.get_value().unwrap(), expected & 1 == 1);
                    }
                    Boolean::Constant(b) => {
                        assert_eq!(b, expected & 1 == 1);
                    }
                }

                expected >>= 1;
            }
        }
    }
}
