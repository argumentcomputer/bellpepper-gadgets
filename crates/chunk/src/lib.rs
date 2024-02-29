use crate::error::ChunkError;
use crate::traits::ChunkStepCircuit;
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
    /// The `ChunkStepCircuit` instance to be used in the `FoldStep`.
    circuit: C,
    /// The step number of the `FoldStep` in the circuit.
    step_nbr: usize,
    /// Number of input to be expected
    input_nbr: usize,
    /// The next input values for the next `ChunkStepCircuit` instance.
    next_input: [F; N],
    /// Next program counter.
    next_pc: F,
}

impl<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> IterationStep<F, C, N> {
    pub fn arity(&self) -> usize {
        N + C::arity()
    }
    pub fn new(
        circuit_index: usize,
        circuit: C,
        inputs: [F; N],
        input_nbr: usize,
        step_nbr: usize,
        next_circuit: F,
    ) -> Self {
        Self {
            circuit_index,
            circuit,
            next_input: inputs,
            input_nbr,
            step_nbr,
            next_pc: next_circuit,
        }
    }

    /// This `synthesize` implementation consists of two parts:
    /// 1. Call the inner synthesize method of `ChunkStepCircuit` with correct inputs.
    /// 2. Calculate the next program and allocate the next input values for the next `FoldStep` instance.
    // Inherited from `StepCircuit`
    #[allow(clippy::type_complexity)]
    pub fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        let (z_in, chunk_in) = z.split_at(C::arity());

        let mut z_out = self.circuit.synthesize(
            &mut cs.namespace(|| format!("chunk_folding_step_{}", self.step_nbr)),
            pc,
            z_in,
            // Only keep inputs that were part of the original input set
            chunk_in,
        )?;

        // Next program
        let next_pc =
            AllocatedNum::alloc_infallible(cs.namespace(|| "next_circuit"), || self.next_pc);

        // Next input
        let next_inputs_allocated = self
            .next_input
            .iter()
            .enumerate()
            .map(|(i, x)| {
                AllocatedNum::alloc(cs.namespace(|| format!("next_input_{i}")), || Ok(*x))
            })
            .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;

        z_out.extend(next_inputs_allocated);
        Ok((Some(next_pc), z_out))
    }

    pub fn from_inputs(
        circuit_index: usize,
        intermediate_steps_input: &[F],
        pc_post_iter: F,
    ) -> anyhow::Result<Vec<Self>> {
        // We generate the `FoldStep` instances that are part of the circuit.
        let mut circuits = intermediate_steps_input
            .chunks(N)
            .enumerate()
            .map(|(i, chunk)| {
                // Create an array filled with F::ZERO
                let mut inputs: [F; N] = [F::ZERO; N];

                // Copy elements from the chunk into the inputs array
                for (input, value) in inputs.iter_mut().zip(chunk.iter()) {
                    *input = *value;
                }

                Ok(IterationStep::new(
                    circuit_index,
                    C::new(),
                    inputs,
                    N,
                    i,
                    F::from(circuit_index as u64),
                ))
            })
            .collect::<anyhow::Result<Vec<_>, ChunkError>>()?;

        // As the input represents the generated values by the inner loop, we need to add one more execution to have
        // a complete circuit and a proper accumulator value.
        circuits.push(IterationStep::new(
            circuit_index,
            C::new(),
            [F::ZERO; N],
            if intermediate_steps_input.len() % N != 0 {
                intermediate_steps_input.len() % N
            } else {
                N
            },
            circuits.len(),
            pc_post_iter,
        ));

        Ok(circuits)
    }
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> Clone for IterationStep<F, C, N> {
    fn clone(&self) -> Self {
        Self {
            circuit_index: self.circuit_index,
            step_nbr: self.step_nbr,
            circuit: self.circuit.clone(),
            next_input: self.next_input,
            next_pc: self.next_pc,
            input_nbr: self.input_nbr,
        }
    }
}
