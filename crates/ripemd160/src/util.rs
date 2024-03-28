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

fn ripemd160_d1<'a, Scalar, CS>(
    mut cs: CS,
    y: &'a Boolean,
    x: &'a Boolean,
    z: &'a Boolean,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let tmp1 = Boolean::and(cs.namespace(|| "x AND y"), x, y)?;
    let tmp2 = Boolean::and(cs.namespace(|| "(!x) AND z"), &x.not(), z)?;
    Boolean::or(cs.namespace(|| "(x AND y) OR ((!x) AND z)"), &tmp1, &tmp2)
}

fn ripemd160_d2<'a, Scalar, CS>(
    mut cs: CS,
    x: &'a Boolean,
    y: &'a Boolean,
    z: &'a Boolean,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    let tmp = Boolean::or(cs.namespace(|| "y OR !z"), y, &z.not())?;
    Boolean::xor(cs.namespace(|| "x XOR (y OR !z)"), x, &tmp)
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
