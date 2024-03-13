use bellpepper::gadgets::uint32::UInt32;
use bellpepper_core::{boolean::AllocatedBit, boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;

fn ripemd160_d1<'a, Scalar, CS>(
    mut cs: CS,
    a: &'a Boolean,
    b: &'a Boolean,
    c: &'a Boolean,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let d1_value = match (a.get_value(), b.get_value(), c.get_value()) {
        (Some(a), Some(b), Some(c)) => {
            // (a and b) xor (a and c) xor (b and c)
            Some((a & b) | (c & !b))
        }
        _ => None,
    };

    match (a, b, c) {
        (&Boolean::Constant(_), &Boolean::Constant(_), &Boolean::Constant(_)) => {
            // They're all constants, so we can just compute the value.

            return Ok(Boolean::Constant(d1_value.expect("they're all constants")));
        }
        (&Boolean::Constant(false), b, c) => {
            // If a is false,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (b and c)
            return Boolean::and(cs, &b.not(), c);
        }
        (_a, &Boolean::Constant(false), c) => {
            // If b is false,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (a and c)
            return Ok(c.clone());
        }
        (a, b, &Boolean::Constant(false)) => {
            // If c is false,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (a and b)
            return Boolean::and(cs, a, b);
        }
        (a, b, &Boolean::Constant(true)) => {
            // If c is true,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (a and b) xor (a) xor (b)
            // equals
            // not ((not a) and (not b))

            return Ok(Boolean::and(cs, &a.not(), b)?.not());
        }
        (a, &Boolean::Constant(true), _c) => {
            // If b is true,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (a) xor (a and c) xor (c)
            return Ok(a.clone());
        }
        (&Boolean::Constant(true), b, c) => {
            // If a is true,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (b) xor (c) xor (b and c)

            return Ok(Boolean::and(cs, &b.not(), &c.not())?.not());
        }
        (
            &Boolean::Is(_) | &Boolean::Not(_),
            &Boolean::Is(_) | &Boolean::Not(_),
            &Boolean::Is(_) | &Boolean::Not(_),
        ) => {}
    }

    let d1 = cs.alloc(
        || "d1",
        || {
            d1_value.ok_or(SynthesisError::AssignmentMissing).map(|v| {
                if v {
                    Scalar::ONE
                } else {
                    Scalar::ZERO
                }
            })
        },
    )?;

    cs.enforce(
        || "d1 computation",
        |_| a.lc(CS::one(), Scalar::ONE) - &c.lc(CS::one(), Scalar::ONE),
        |_| b.lc(CS::one(), Scalar::ONE),
        |lc| lc + d1 - &c.lc(CS::one(), Scalar::ONE),
    );

    Ok(AllocatedBit::alloc(cs.namespace(|| "d1"), d1_value)
        .unwrap()
        .into())
}

fn ripemd160_d2<'a, Scalar, CS>(
    mut cs: CS,
    a: &'a Boolean,
    b: &'a Boolean,
    c: &'a Boolean,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let d2_value = match (a.get_value(), b.get_value(), c.get_value()) {
        (Some(a), Some(b), Some(c)) => {
            // (a)xor(b or not(c))
            Some((a) ^ (b | !c))
        }
        _ => None,
    };

    match (a, b, c) {
        (&Boolean::Constant(_), &Boolean::Constant(_), &Boolean::Constant(_)) => {
            // They're all constants, so we can just compute the value.

            return Ok(Boolean::Constant(d2_value.expect("they're all constants")));
        }
        (&Boolean::Constant(false), b, c) => {
            // If a is false,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (b and c)
            return Ok(Boolean::and(cs, c, &b.not())?.not());
        }
        (a, &Boolean::Constant(false), c) => {
            // If b is false,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (a and c)

            return Boolean::xor(cs, a, &c.not());
        }
        (a, _b, &Boolean::Constant(false)) => {
            // If c is false,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (a and b)
            return Ok(Boolean::and(cs, a, a)?.not());
        }
        (a, b, &Boolean::Constant(true)) => {
            // If c is true,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (a and b) xor (a) xor (b)
            // equals
            // not ((not a) and (not b))

            return Boolean::xor(cs, a, b);
        }
        (a, &Boolean::Constant(true), _c) => {
            // If b is true,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (a) xor (a and c) xor (c)
            return Ok(Boolean::and(cs, a, a)?.not());
        }
        (&Boolean::Constant(true), b, c) => {
            // If a is true,
            // (a and b) xor (a and c) xor (b and c)
            // equals
            // (b) xor (c) xor (b and c)
            return Boolean::and(cs, c, &b.not());
        }
        (
            &Boolean::Is(_) | &Boolean::Not(_),
            &Boolean::Is(_) | &Boolean::Not(_),
            &Boolean::Is(_) | &Boolean::Not(_),
        ) => {}
    }

    let d2 = cs.alloc(
        || "d2",
        || {
            d2_value.ok_or(SynthesisError::AssignmentMissing).map(|v| {
                if v {
                    Scalar::ONE
                } else {
                    Scalar::ZERO
                }
            })
        },
    )?;

    let notbc = Boolean::and(cs.namespace(|| "not b and c"), &b.not(), c)?;

    cs.enforce(
        || "d2 computation",
        |lc| lc + CS::one() - &a.lc(CS::one(), Scalar::ONE),
        |lc| {
            lc + CS::one() + &b.lc(CS::one(), Scalar::ONE)
                - &c.lc(CS::one(), Scalar::ONE)
                - &notbc.lc(CS::one(), Scalar::ONE)
        },
        |lc| lc + d2 - &notbc.lc(CS::one(), Scalar::ONE),
    );

    Ok(AllocatedBit::alloc(cs.namespace(|| "d2"), d2_value)
        .unwrap()
        .into())
}

pub fn shl_uint32(a: &UInt32, by: usize) -> Result<UInt32, SynthesisError> {
    let by = by % 32;

    let fill = Boolean::constant(false);
    let new_bits: Vec<_> = std::iter::repeat(&fill)
        .take(by)
        .chain(a.clone().into_bits().iter()) // The bits are least significant first
        .take(32) // Only 32 bits needed!
        .cloned()
        .collect();
    Ok(UInt32::from_bits(&new_bits))
}

fn triop<Scalar, CS, U>(
    mut cs: CS,
    a: &UInt32,
    b: &UInt32,
    c: &UInt32,
    circuit_fn: U,
) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
    U: Fn(&mut CS, usize, &Boolean, &Boolean, &Boolean) -> Result<Boolean, SynthesisError>,
{
    let bits: Vec<_> = a
        .clone()
        .into_bits()
        .iter()
        .zip(b.clone().into_bits().iter())
        .zip(c.clone().into_bits().iter())
        .enumerate()
        .map(|(i, ((a, b), c))| circuit_fn(&mut cs, i, a, b, c))
        .collect::<Result<_, _>>()?;

    Ok(UInt32::from_bits(&bits))
}

pub fn ripemd_d1<Scalar, CS>(
    cs: CS,
    a: &UInt32,
    b: &UInt32,
    c: &UInt32,
) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    triop(cs, a, b, c, |cs, i, a, b, c| {
        ripemd160_d1(cs.namespace(|| format!("d1 {}", i)), a, b, c)
    })
}

pub fn ripemd_d2<Scalar, CS>(
    cs: CS,
    a: &UInt32,
    b: &UInt32,
    c: &UInt32,
) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    triop(cs, a, b, c, |cs, i, a, b, c| {
        ripemd160_d2(cs.namespace(|| format!("d2 {}", i)), a, b, c)
    })
}

#[cfg(test)]
mod test {

    use bellpepper_core::test_cs::TestConstraintSystem;
    use pasta_curves::Fp;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    use super::*;

    #[test]
    fn test_uint32_shl() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..50 {
            for i in 0..60 {
                let mut cs = TestConstraintSystem::<Fp>::new();
                let num = rng.next_u32();
                let mut expected = num.wrapping_shl(i as u32);
                let num_bit = UInt32::alloc(cs.namespace(|| "num_bit"), Some(num)).unwrap();
                let res = shl_uint32(&num_bit, i).unwrap();
                for b in res.into_bits() {
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

    #[test]
    fn test_uint32_ripemd_d1() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let a = rng.next_u32();
            let b = rng.next_u32();
            let c = rng.next_u32();

            let mut expected = (a & b) | ((!b) & c);

            let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = ripemd_d1(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            for b in r.into_bits().iter() {
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
    fn test_uint32_ripemd_d2() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let a = rng.next_u32();
            let b = rng.next_u32();
            let c = rng.next_u32();

            let mut expected = (a) ^ ((b) | !c);

            let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = ripemd_d2(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            for b in r.into_bits().iter() {
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
