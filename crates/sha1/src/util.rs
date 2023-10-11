use bellpepper::gadgets::uint32::UInt32;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

/// Perform OR over two boolean operands
pub fn or_boolean<'a, Scalar, CS>(
    cs: CS,
    a: &'a Boolean,
    b: &'a Boolean,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    match (a, b) {
        // true OR x is always true
        (&Boolean::Constant(true), _) | (_, &Boolean::Constant(true)) => {
            Ok(Boolean::Constant(true))
        }
        // false OR x is always x
        (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
        // a OR (NOT b)
        (&Boolean::Is(ref is), &Boolean::Not(ref not))
        | (&Boolean::Not(ref not), &Boolean::Is(ref is)) => {
            Ok(Boolean::Is(or_not_allocated_bits(cs, is, not)?))
        }
        // (NOT a) OR (NOT b) = a NOR b
        (Boolean::Not(a), Boolean::Not(b)) => Ok(Boolean::Is(nand_allocated_bits(cs, a, b)?)),
        // a OR b
        (Boolean::Is(a), Boolean::Is(b)) => Ok(Boolean::Is(or_allocated_bits(cs, a, b)?)),
    }
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
    let and_bits = a_bits
        .iter()
        .zip(b_bits.iter())
        .enumerate()
        .map(|(i, (x, y))| or_boolean(cs.namespace(|| format!("or {i}")), x, y).unwrap())
        .collect::<Vec<_>>();

    Ok(UInt32::from_bits(&and_bits))
}

/// Calculates `a OR (NOT b)`.
pub fn or_not_allocated_bits<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedBit,
    b: &AllocatedBit,
) -> Result<AllocatedBit, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let result_value = a
        .get_value()
        .zip(b.get_value())
        .map(|(a_val, b_val)| a_val | !b_val);

    let result_bit = AllocatedBit::alloc(cs.namespace(|| "or not result"), result_value)?;

    // Constrain (1-a) * (b) = (1-c), ensuring c is 0 iff
    // a is false and b is true, and otherwise c is 1.
    cs.enforce(
        || "or not constraint",
        |lc| lc + CS::one() - a.get_variable(),
        |lc| lc + b.get_variable(),
        |lc| lc + CS::one() - result_bit.get_variable(),
    );

    Ok(result_bit)
}

/// Calculates `NOT(a AND b) = (NOT a) OR (NOT b)`.
pub fn nand_allocated_bits<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedBit,
    b: &AllocatedBit,
) -> Result<AllocatedBit, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let result_value = a
        .get_value()
        .zip(b.get_value())
        .map(|(a_val, b_val)| !(a_val & b_val));

    let result_bit = AllocatedBit::alloc(cs.namespace(|| "nand result"), result_value)?;

    // Constrain (a) * (b) = (1-c), ensuring c is 0 iff
    // a and b are both true, and otherwise c is 1.
    cs.enforce(
        || "nand constraint",
        |lc| lc + a.get_variable(),
        |lc| lc + b.get_variable(),
        |lc| lc + CS::one() - result_bit.get_variable(),
    );

    Ok(result_bit)
}

/// Calculates `NOT(a AND b) = (NOT a) OR (NOT b)`.
pub fn or_allocated_bits<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedBit,
    b: &AllocatedBit,
) -> Result<AllocatedBit, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let result_value = a
        .get_value()
        .zip(b.get_value())
        .map(|(a_val, b_val)| a_val | b_val);

    let result_bit = AllocatedBit::alloc(cs.namespace(|| "or result"), result_value)?;

    // Constrain (1 - a) * (1 - b) = (1-c), ensuring c is 0 iff
    // a and b are both false, and otherwise c is 1.
    cs.enforce(
        || "or constraint",
        |lc| lc + CS::one() - a.get_variable(),
        |lc| lc + CS::one() - b.get_variable(),
        |lc| lc + CS::one() - result_bit.get_variable(),
    );

    Ok(result_bit)
}

#[cfg(test)]
mod test {

    use bellpepper_core::test_cs::TestConstraintSystem;
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
                        Boolean::Is(ref v),
                    ) => {
                        // assert!(cs.get("or result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        // assert!(cs.get("or result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        // assert!(cs.get("or not result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        // assert!(cs.get("or not result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        // assert!(cs.get("or result") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("or result/boolean") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("or not result/boolean") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("or not result/boolean") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
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
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("or not result/boolean") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("or not result/boolean") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nand result/boolean") == Field::ZERO);
                        assert_eq!(v.get_value(), Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nand result/boolean") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
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
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("or not result/boolean") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("or not result/boolean") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nand result/boolean") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nand result/boolean") == Field::ONE);
                        assert_eq!(v.get_value(), Some(true));
                    }

                    _ => panic!("this should never be encountered"),
                }
            }
        }
    }
}
