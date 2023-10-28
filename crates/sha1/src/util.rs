use bellpepper::gadgets::uint32::UInt32;
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;

/// AND two `UInt32` variables
pub fn and_uint32<Scalar, CS>(mut cs: CS, a: &UInt32, b: &UInt32) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let a_bits = a.clone().into_bits();
    let b_bits = b.clone().into_bits();
    let and_bits = a_bits
        .iter()
        .zip(b_bits.iter())
        .enumerate()
        .map(|(i, (x, y))| Boolean::and(cs.namespace(|| format!("and {i}")), x, y).unwrap())
        .collect::<Vec<_>>();

    Ok(UInt32::from_bits(&and_bits))
}

/// OR two `UInt32` variables
pub fn or_uint32<Scalar, CS>(mut cs: CS, a: &UInt32, b: &UInt32) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let a_bits = a.clone().into_bits();
    let b_bits = b.clone().into_bits();
    let or_bits = a_bits
        .iter()
        .zip(b_bits.iter())
        .enumerate()
        .map(|(i, (x, y))| Boolean::or(cs.namespace(|| format!("or {i}")), x, y).unwrap())
        .collect::<Vec<_>>();

    Ok(UInt32::from_bits(&or_bits))
}

#[cfg(test)]
mod test {

    use bellpepper_core::test_cs::TestConstraintSystem;
    use pasta_curves::Fp;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    use super::*;

    #[test]
    fn test_uint32_and() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let a = rng.next_u32();
            let b = rng.next_u32();
            let c = rng.next_u32();

            let mut expected = a & b & c;

            let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = and_uint32(cs.namespace(|| "first and"), &a_bit, &b_bit).unwrap();
            let r = and_uint32(cs.namespace(|| "second and"), &r, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            for b in r.into_bits() {
                match b {
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
    fn test_uint32_or() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let a = rng.next_u32();
            let b = rng.next_u32();
            let c = rng.next_u32();

            let mut expected = a | b | c;

            let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = or_uint32(cs.namespace(|| "first or"), &a_bit, &b_bit).unwrap();
            let r = or_uint32(cs.namespace(|| "second or"), &r, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            for b in r.into_bits() {
                match b {
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
