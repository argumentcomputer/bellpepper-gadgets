use crate::error::ChunkError;
use crate::traits::{ChunkCircuit, ChunkStepCircuit};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use getset::Getters;
use std::convert::TryInto;

pub mod error;
pub mod traits;

/// `FoldStep` is the wrapper struct for a `ChunkStepCircuit` implemented by a user. It exist to synthesize multiple of
/// the `ChunkStepCircuit` instances at once.
#[derive(Eq, PartialEq, Debug, Getters)]
#[getset(get = "pub")]
pub struct FoldStep<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> {
    /// The step number of the `FoldStep` in the circuit.
    step_nbr: usize,
    /// The `ChunkStepCircuit` instance to be used in the `FoldStep`.
    circuit: C,
    /// The next input values for the next `ChunkStepCircuit` instance.
    next_input: [F; N],
}

impl<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> FoldStep<F, C, N> {
    pub fn arity(&self) -> usize {
        N + C::arity()
    }
    pub fn new(circuit: C, inputs: [F; N], step_nbr: usize) -> Self {
        Self {
            circuit,
            next_input: inputs,
            step_nbr,
        }
    }

    /// This `synthesize` implementation consists of two parts:
    /// 1. Synthesize the necessary number of `ChunkStepCircuit` instances.
    /// 2. Allocate the next input values for the next `FoldStep` instance.
    pub fn synthesize<CS: ConstraintSystem<F>>(
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

        z_out.extend(next_inputs_allocated);
        Ok(z_out)
    }
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> Clone for FoldStep<F, C, N> {
    fn clone(&self) -> Self {
        Self {
            step_nbr: self.step_nbr,
            circuit: self.circuit.clone(),
            next_input: self.next_input,
        }
    }
}

/// `Circuit` is a helper structure that handles the plumbing of generating the necessary number of `FoldStep` instances
/// to properly prove and verifiy a circuit.
#[derive(Debug, Getters)]
pub struct Circuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    /// The `FoldStep` instances that are part of the circuit.
    #[getset(get = "pub")]
    circuits: Vec<FoldStep<F, C, N>>,
    /// The number of folding step required in the recursive snark to prove and verify the circuit.
    num_fold_steps: usize,
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> ChunkCircuit<F, C, N>
    for Circuit<F, C, N>
{
    fn new(intermediate_steps_input: &[F]) -> anyhow::Result<Self, ChunkError> {
        // For now, we can only handle inputs that are a multiple of N.
        if intermediate_steps_input.len() % N != 0 {
            return Err(ChunkError::InvalidInputLength(
                intermediate_steps_input.len(),
                N,
            ));
        }

        // We generate the `FoldStep` instances that are part of the circuit.
        let mut circuits = intermediate_steps_input
            .chunks(N)
            .enumerate()
            .map(|(i, chunk)| {
                let inputs: [F; N] = chunk
                    .try_into()
                    .map_err(|err| ChunkError::DivisionError { source: err })?;

                Ok(FoldStep::new(C::new(), inputs, i))
            })
            .collect::<anyhow::Result<Vec<_>, ChunkError>>()?;

        // As the input represents the generated values by the inner loop, we need to add one more execution to have
        // a complete circuit and a proper accumulator value.
        circuits.push(FoldStep::new(C::new(), [F::ZERO; N], circuits.len()));

        Ok(Self {
            circuits,
            num_fold_steps: (intermediate_steps_input.len() / N) + 1,
        })
    }

    fn initial_input(&self) -> Option<&FoldStep<F, C, N>> {
        self.circuits.first()
    }

    fn num_fold_steps(&self) -> usize {
        self.num_fold_steps
    }
}
