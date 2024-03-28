use bellpepper::gadgets::uint32::UInt32;
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;

pub fn swap_byte_endianness(bits: &Vec<Boolean>) -> Vec<Boolean> {
    assert!(bits.len() % 8 == 0);
    let mut modified_bits = vec![];
    for i in 0..bits.len() / 8 {
        for j in 0..8 {
            modified_bits.push(bits[i * 8 + 7 - j].clone());
        }
    }
    modified_bits
}

pub fn uint32_rotl(a: UInt32, by: usize) -> UInt32 {
    assert!(by < 32usize);
    a.rotr(32 - by)
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

pub fn f1<Scalar, CS>(
    mut cs: CS,
    x: &UInt32,
    y: &UInt32,
    z: &UInt32,
) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let res = x.xor(cs.namespace(|| "x XOR y"), y)?;
    res.xor(cs.namespace(|| "x XOR y XOR z"), z)
}

fn f2_boolean<Scalar, CS>(
    mut cs: CS,
    x: &Boolean,
    y: &Boolean,
    z: &Boolean,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let tmp1 = Boolean::and(cs.namespace(|| "x AND y"), x, y)?;
    let tmp2 = Boolean::and(cs.namespace(|| "(!x) AND z"), &x.not(), z)?;
    Boolean::or(cs.namespace(|| "(x AND y) OR ((!x) AND z)"), &tmp1, &tmp2)
}

pub fn f2<Scalar, CS>(cs: CS, x: &UInt32, y: &UInt32, z: &UInt32) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    triop(cs, x, y, z, |cs, i, a, b, c| {
        f2_boolean(cs.namespace(|| format!("f2 {}", i)), a, b, c)
    })
}

fn f3_boolean<Scalar, CS>(
    mut cs: CS,
    x: &Boolean,
    y: &Boolean,
    z: &Boolean,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let tmp = Boolean::or(cs.namespace(|| "x OR !y"), x, &y.not())?;
    Boolean::xor(cs.namespace(|| "(x OR !y) XOR z"), &tmp, z)
}

pub fn f3<Scalar, CS>(cs: CS, x: &UInt32, y: &UInt32, z: &UInt32) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    triop(cs, x, y, z, |cs, i, a, b, c| {
        f3_boolean(cs.namespace(|| format!("f3 {}", i)), a, b, c)
    })
}

pub fn f4<Scalar, CS>(cs: CS, x: &UInt32, y: &UInt32, z: &UInt32) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    triop(cs, x, y, z, |cs, i, a, b, c| {
        f2_boolean(cs.namespace(|| format!("f4 {}", i)), c, a, b)
    })
}

pub fn f5<Scalar, CS>(cs: CS, x: &UInt32, y: &UInt32, z: &UInt32) -> Result<UInt32, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    triop(cs, x, y, z, |cs, i, a, b, c| {
        f3_boolean(cs.namespace(|| format!("f5 {}", i)), b, c, a)
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
    fn test_swap_byte_endianness() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..50 {
            let a = rng.next_u32();
            let a_le_bytes = a.to_le_bytes();
            let a_rev_le_bytes = a_le_bytes.map(|b| b.reverse_bits());
            let a_rev = u32::from_le_bytes(a_rev_le_bytes);

            let a_bits = UInt32::constant(a).into_bits_be();
            let a_rev_bits = UInt32::constant(a_rev).into_bits_be();
            let a_rev_bits_exp = swap_byte_endianness(&a_bits);

            for (x, y) in a_rev_bits.into_iter().zip(a_rev_bits_exp.into_iter()) {
                assert_eq!(x.get_value().unwrap(), y.get_value().unwrap());
            }
        }
    }

    #[test]
    fn test_uint32_f2() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let a = rng.next_u32();
            let b = rng.next_u32();
            let c = rng.next_u32();

            let mut expected = (a & b) | ((!a) & c);

            let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = f2(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

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
    fn test_uint32_f4() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let a = rng.next_u32();
            let b = rng.next_u32();
            let c = rng.next_u32();

            let mut expected = (a & c) | (b & !c);

            let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = f4(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

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
    fn test_uint32_f3() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let a = rng.next_u32();
            let b = rng.next_u32();
            let c = rng.next_u32();

            let mut expected = ((a) | !b) ^ c;

            let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = f3(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

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
    fn test_uint32_f5() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let a = rng.next_u32();
            let b = rng.next_u32();
            let c = rng.next_u32();

            let mut expected = a ^ (b | !c);

            let a_bit = UInt32::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = f5(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

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
