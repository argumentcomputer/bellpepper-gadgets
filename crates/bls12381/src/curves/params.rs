use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, SynthesisError,
};
use bellpepper_emulated::field_element::{
    EmulatedFieldElement, EmulatedFieldParams, PseudoMersennePrime,
};
use bls12_381::fp::Fp as BlsFp;
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::{BigInt, Sign};

pub struct CurveParams {
    A: BigInt,
    B: BigInt,
    Gx: BigInt,
    Gy: BigInt,
    Gm: Vec<[BigInt; 2]>,
    Eigenvalue: BigInt,
    ThirdRootOne: BigInt,
}

pub trait EmulatedCurveParams {
    fn a() -> BigInt;
    fn b() -> BigInt;
}
