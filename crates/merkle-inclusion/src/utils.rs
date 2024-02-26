use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::Itertools;
use std::ops::Sub;

pub fn conditionally_select_bool<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Boolean,
    b: &Boolean,
    condition: &Boolean,
) -> Result<Boolean, SynthesisError> {
    let value = if condition.get_value().unwrap_or_default() {
        a.get_value()
    } else {
        b.get_value()
    };

    let result = Boolean::Is(AllocatedBit::alloc(
        &mut cs.namespace(|| "conditional select result"),
        value,
    )?);

    cs.enforce(
        || "conditional select constraint",
        |_| condition.lc(CS::one(), F::ONE),
        |_| a.lc(CS::one(), F::ONE).sub(&b.lc(CS::one(), F::ONE)),
        |_| result.lc(CS::one(), F::ONE).sub(&b.lc(CS::one(), F::ONE)),
    );

    Ok(result)
}

/// If condition return a otherwise b
pub fn conditionally_select_vec<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &[Boolean],
    b: &[Boolean],
    condition: &Boolean,
) -> Result<Vec<Boolean>, SynthesisError> {
    a.iter()
        .zip_eq(b.iter())
        .enumerate()
        .map(|(i, (a, b))| {
            conditionally_select_bool(cs.namespace(|| format!("select_{i}")), a, b, condition)
        })
        .collect::<Result<Vec<Boolean>, SynthesisError>>()
}
