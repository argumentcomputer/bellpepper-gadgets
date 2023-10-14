use bellpepper::gadgets::uint32::UInt32;
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;

/// Perform OR over two boolean operands
pub fn or_boolean<'a, Scalar, CS>(
    mut cs: CS,
    a: &'a Boolean,
    b: &'a Boolean,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    Ok(Boolean::not(&Boolean::and(
        cs.namespace(|| "not and (not a) (not b)"),
        &Boolean::not(a),
        &Boolean::not(b),
    )?))
}

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
        .map(|(i, (x, y))| or_boolean(cs.namespace(|| format!("or {i}")), x, y).unwrap())
        .collect::<Vec<_>>();

    Ok(UInt32::from_bits(&or_bits))
}

#[cfg(test)]
mod test {

    use bellpepper_core::{boolean::AllocatedBit, test_cs::TestConstraintSystem};
    use ff::Field;
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

    #[derive(Copy, Clone, Debug)]
    enum OperandType {
        True,
        False,
        AllocatedTrue,
        AllocatedFalse,
        NegatedAllocatedTrue,
        NegatedAllocatedFalse,
    }

    #[test]
    fn test_boolean_or() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TestConstraintSystem::<Fp>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap()).not()
                            }
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = or_boolean(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c.clone()) {
                    (OperandType::True, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Constant(true)) => {}
                    (
                        OperandType::True,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Constant(true),
                    ) => {}
                    (
                        OperandType::True,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Constant(true),
                    ) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/nor result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/nor result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and not result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and not result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/nor result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/nor result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and not result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and not result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }

                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::True,
                        Boolean::Constant(true),
                    ) => {}
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and not result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and not result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }

                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::True,
                        Boolean::Constant(true),
                    ) => {}
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and not result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and not result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("not and (not a) (not b)/and result") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }

                    _ => panic!("this should never be encountered"),
                }
            }
        }
    }
}
