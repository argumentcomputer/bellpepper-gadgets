//! Circuit representation of a [`u64`], with helpers for the [`keccak256`]
//! gadgets.
//!
// TODO: consider upstreaming to Bellpepper

use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, SynthesisError};
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

        UInt64 {
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

        Ok(UInt64 { bits, value })
    }

    #[allow(dead_code)]
    pub fn into_bits_be(self) -> Vec<Boolean> {
        let mut ret = self.bits;
        ret.reverse();
        ret
    }

    #[allow(dead_code)]
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

        UInt64 {
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

        UInt64 {
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

        UInt64 {
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

        UInt64 {
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

        Ok(UInt64 {
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

        Ok(UInt64 {
            bits,
            value: new_value,
        })
    }

    /// NOT this `UInt64`
    pub fn not(&self) -> Self {
        let new_value = self.value.map(|a| !a);

        let bits = self.bits.iter().map(|a| a.not()).collect();

        UInt64 {
            bits,
            value: new_value,
        }
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
    use bellpepper_core::boolean::Boolean;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bellpepper_core::ConstraintSystem;
    use bls12_381::Bls12;

    use bitvec::prelude::*;
    use proptest::prelude::*;
    use std::convert::TryInto;

    proptest! {
        #[test]
        fn test_uint64_from_constant(a: u64) {
            let b = UInt64::constant(a);
            assert_eq!(a, b.value.unwrap());
        }

        #[test]
        fn test_uint64_from_bits_be(a: u64) {
            let a_bv = BitVec::<Msb0, u64>::from_element(a);
            let a_bits: Vec<Boolean> = a_bv.iter().map(|b| Boolean::constant(*b)).collect();
            let b = UInt64::from_bits_be(&a_bits);
            assert_eq!(a, b.value.unwrap());
        }

        #[test]
        fn test_uint64_from_bits(a: u64) {
            let a_bv = BitVec::<Lsb0, u64>::from_element(a);
            let a_bits: Vec<Boolean> = a_bv.iter().map(|b| Boolean::constant(*b)).collect();
            let b = UInt64::from_bits(&a_bits);
            assert_eq!(a, b.value.unwrap());
        }

        #[test]
        fn test_uint64_xor(a: u64, b: u64, c: u64) {
            let mut cs = TestConstraintSystem::<<Bls12 as pairing::Engine>::Fr>::new();

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
}
