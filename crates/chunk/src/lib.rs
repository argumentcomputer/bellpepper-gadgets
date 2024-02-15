use crate::error::ChunkError;
use crate::traits::{ChunkCircuit, ChunkStepCircuit};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use nova::traits::circuit::StepCircuit;
use std::convert::TryInto;

pub mod error;
pub mod traits;

pub struct FoldStep<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> {
    step_nbr: usize,
    circuit: C,
    next_input: [F; N],
}

impl<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> FoldStep<F, C, N> {
    pub fn new(circuit: C, inputs: [F; N], step_nbr: usize) -> Self {
        Self {
            circuit,
            next_input: inputs,
            step_nbr,
        }
    }
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> Clone for FoldStep<F, C, N> {
    fn clone(&self) -> Self {
        FoldStep {
            step_nbr: self.step_nbr,
            circuit: self.circuit.clone(),
            next_input: self.next_input.clone(),
        }
    }
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> StepCircuit<F> for FoldStep<F, C, N> {
    fn arity(&self) -> usize {
        N + C::arity()
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let (z_in, chunk_in) = z.split_at(C::arity());
        let mut z_out = self.circuit.chunk_synthesize(
            &mut cs.namespace(|| format!("chunk_folding_step_{}", self.step_nbr)),
            z_in,
            chunk_in,
        )?;

        let next_inputs_allocated = self
            .next_input
            .iter()
            .enumerate()
            .map(|(i, x)| {
                AllocatedNum::alloc(cs.namespace(|| format!("next_input_{i}")), || Ok(*x))
            })
            .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;

        z_out.extend(next_inputs_allocated.into_iter());
        Ok(z_out)
    }
}

pub struct Circuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    circuits: Vec<FoldStep<F, C, N>>,
    num_fold_steps: usize,
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> Circuit<F, C, N> {
    pub fn circuits(&self) -> &[FoldStep<F, C, N>] {
        &self.circuits
    }
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> ChunkCircuit<F, C, N>
    for Circuit<F, C, N>
{
    // TODO use z0_primary for accumulator initialization
    fn new(z0_primary: &[F], intermediate_steps_input: &[F]) -> anyhow::Result<Self, ChunkError> {
        if intermediate_steps_input.len() % N != 0 {
            return Err(ChunkError::InvalidInputLength(
                intermediate_steps_input.len(),
                N,
            ));
        }

        Ok(Self {
            circuits: (0..intermediate_steps_input.len())
                .step_by(N)
                .map(|i| {
                    let inputs: [F; N] = intermediate_steps_input[i..i + N]
                        .try_into()
                        .map_err(|err| ChunkError::DivisionError { source: err })?;
                    Ok(FoldStep::new(C::new(), inputs, i))
                })
                .collect::<anyhow::Result<Vec<_>, ChunkError>>()?,
            num_fold_steps: intermediate_steps_input.len() / N,
        })
    }

    fn initial_input(&self) -> Option<&FoldStep<F, C, N>> {
        self.circuits.get(0)
    }

    fn num_fold_steps(&self) -> usize {
        self.num_fold_steps
    }
}
