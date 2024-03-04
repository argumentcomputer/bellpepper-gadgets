use crate::error::ChunkError;
use crate::traits::ChunkStepCircuit;
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use getset::Getters;

pub mod error;
pub mod traits;

/// `IterationStep` is the wrapper struct for a `ChunkStepCircuit` implemented by a user.
#[derive(Eq, PartialEq, Debug, Getters)]
#[getset(get = "pub")]
pub struct IterationStep<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> {
    /// The circuit index in the higher order `NonUniformCircuit`.
    circuit_index: usize,
    /// The `ChunkStepCircuit` instance to be used in the `IterationStep`.
    circuit: C,
    /// The step number of the `IterationStep` in the circuit.
    step_nbr: usize,
    /// Number of input to be expected
    input_nbr: usize,
    /// The next input values for the next `ChunkStepCircuit` instance.
    inputs: [F; N],
    /// Next program counter.
    next_pc: F,
}

impl<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> IterationStep<F, C, N> {
    pub fn arity(&self) -> usize {
        C::arity()
    }
    pub fn new(
        circuit_index: usize,
        circuit: C,
        inputs: [F; N],
        input_nbr: usize,
        step_nbr: usize,
        next_pc: F,
    ) -> Self {
        Self {
            circuit_index,
            circuit,
            inputs,
            input_nbr,
            step_nbr,
            next_pc,
        }
    }

    /// This `synthesize` implementation consists of two parts:
    /// 1. Call the inner synthesize method of `ChunkStepCircuit` with correct inputs.
    /// 2. Calculate the next program and allocate the next input values for the next `IterationStep` instance.
    // Inherited from `StepCircuit`
    #[allow(clippy::type_complexity)]
    pub fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        let valid_inputs = self
            .inputs
            .iter()
            .enumerate()
            .map(|(i, input)| {
                let valid = Boolean::Is(
                    AllocatedBit::alloc(
                        cs.namespace(|| {
                            format!("iteration step {} valid_input_{i}", self.step_nbr)
                        }),
                        Some(i < self.input_nbr),
                    )
                    .unwrap(),
                );
                (valid, *input)
            })
            .collect::<Vec<_>>();

        let z_out = self.circuit.synthesize(
            &mut cs.namespace(|| format!("chunk_iterating_step_{}", self.step_nbr)),
            pc,
            z,
            // Only keep inputs that were part of the original input set
            &valid_inputs,
        )?;

        // Next program
        let next_pc = AllocatedNum::alloc_infallible(
            cs.namespace(|| format!("next_program_counter iteration step {}", self.input_nbr)),
            || self.next_pc,
        );

        Ok((Some(next_pc), z_out))
    }

    pub fn from_inputs(
        circuit_index: usize,
        intermediate_steps_input: &[F],
        pc_post_iter: F,
    ) -> anyhow::Result<Vec<Self>> {
        // We generate the `IterationStep` instances that are part of the circuit.
        let circuits = intermediate_steps_input
            .chunks(N)
            .enumerate()
            .map(|(i, chunk)| {
                // Create an array filled with F::ZERO
                let mut inputs: [F; N] = [F::ZERO; N];

                // Copy elements from the chunk into the inputs array
                for (value, input) in chunk.iter().zip(inputs.iter_mut()) {
                    *input = *value;
                }

                let next_circuit = if i == intermediate_steps_input.len().div_ceil(N) - 1 {
                    pc_post_iter
                } else {
                    F::from(circuit_index as u64)
                };

                Ok(Self::new(
                    circuit_index,
                    C::new(),
                    inputs,
                    chunk.len(),
                    i,
                    next_circuit,
                ))
            })
            .collect::<anyhow::Result<Vec<_>, ChunkError>>()?;

        Ok(circuits)
    }
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> Clone for IterationStep<F, C, N> {
    fn clone(&self) -> Self {
        Self {
            circuit_index: self.circuit_index,
            step_nbr: self.step_nbr,
            circuit: self.circuit.clone(),
            inputs: self.inputs,
            next_pc: self.next_pc,
            input_nbr: self.input_nbr,
        }
    }
}
