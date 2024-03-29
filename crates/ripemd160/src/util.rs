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

    macro_rules! test_helper_function {
        ($test_name:ident, $func:ident, $expected_res_calculator:expr) => {
            #[test]
            fn $test_name() {
                let mut rng = XorShiftRng::from_seed([
                    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54,
                    0x06, 0xbc, 0xe5,
                ]);

                for _ in 0..1000 {
                    let mut cs = TestConstraintSystem::<Fp>::new();

                    let a = rng.next_u32();
                    let b = rng.next_u32();
                    let c = rng.next_u32();

                    let mut expected = $expected_res_calculator(a, b, c);

                    let a_uint32 = UInt32::alloc(cs.namespace(|| "alloc a"), Some(a)).unwrap();
                    let b_uint32 = UInt32::alloc(cs.namespace(|| "alloc b"), Some(b)).unwrap();
                    let c_uint32 = UInt32::alloc(cs.namespace(|| "alloc c"), Some(c)).unwrap();

                    let res = $func(&mut cs, &a_uint32, &b_uint32, &c_uint32).unwrap();

                    assert!(cs.is_satisfied());

                    for x in res.into_bits().iter() {
                        assert_eq!(x.get_value().unwrap(), expected & 1 == 1);
                        expected >>= 1;
                    }
                }
            }
        };
    }

    test_helper_function!(test_uint32_f1, f1, |a: u32, b: u32, c: u32| { a ^ b ^ c });
    test_helper_function!(test_uint32_f2, f2, |a: u32, b: u32, c: u32| {
        (a & b) | ((!a) & c)
    });
    test_helper_function!(test_uint32_f3, f3, |a: u32, b: u32, c: u32| {
        ((a) | !b) ^ c
    });
    test_helper_function!(test_uint32_f4, f4, |a: u32, b: u32, c: u32| {
        (a & c) | (b & !c)
    });
    test_helper_function!(test_uint32_f5, f5, |a: u32, b: u32, c: u32| {
        a ^ (b | !c)
    });
}
