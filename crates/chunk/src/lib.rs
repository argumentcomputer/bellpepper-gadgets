use crate::error::ChunkError;
use crate::traits::{ChunkCircuitInner, ChunkStepCircuit};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use getset::Getters;

pub mod error;
pub mod traits;

/// `FoldStep` is the wrapper struct for a `ChunkStepCircuit` implemented by a user. It exist to synthesize multiple of
/// the `ChunkStepCircuit` instances at once.
#[derive(Eq, PartialEq, Debug, Getters)]
#[getset(get = "pub")]
pub struct FoldStep<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> {
    /// The step number of the `FoldStep` in the circuit.
    step_nbr: usize,
    /// Next circuit index.
    next_circuit: Option<F>,
    /// The `ChunkStepCircuit` instance to be used in the `FoldStep`.
    circuit: C,
    /// Number of input to be expected
    input_nbr: usize,
    /// The next input values for the next `ChunkStepCircuit` instance.
    next_input: [F; N],
}

impl<F: PrimeField, C: ChunkStepCircuit<F> + Clone, const N: usize> FoldStep<F, C, N> {
    pub fn arity(&self) -> usize {
        N + C::arity()
    }
    pub fn new(
        circuit: C,
        inputs: [F; N],
        input_nbr: usize,
        step_nbr: usize,
        next_circuit: Option<F>,
    ) -> Self {
        Self {
            circuit,
            next_input: inputs,
            input_nbr,
            step_nbr,
            next_circuit,
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

        let mut z_out = self.circuit.chunk_synthesize(
            &mut cs.namespace(|| format!("chunk_folding_step_{}", self.step_nbr)),
            pc,
            z_in,
            // Only keep inputs that were part of the original input set
            chunk_in.split_at(self.input_nbr).0,
        )?;

        // Next program
        let next_pc = match self.next_circuit() {
            Some(next_circuit) => {
                AllocatedNum::alloc(cs.namespace(|| "next_circuit"), || Ok(*next_circuit))?
            }
            None => AllocatedNum::alloc(cs.namespace(|| "next_circuit"), || Ok(F::ZERO))?,
        };

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
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> Clone for FoldStep<F, C, N> {
    fn clone(&self) -> Self {
        Self {
            step_nbr: self.step_nbr,
            circuit: self.circuit.clone(),
            next_input: self.next_input,
            next_circuit: self.next_circuit,
            input_nbr: self.input_nbr,
        }
    }
}

/// `Circuit` is a helper structure that handles the plumbing of generating the necessary number of `FoldStep` instances
/// to properly prove and verifiy a circuit.
#[derive(Debug, Getters)]
pub struct InnerCircuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    /// The `FoldStep` instances that are part of the circuit.
    #[getset(get = "pub")]
    circuits: Vec<FoldStep<F, C, N>>,
    /// The number of folding step required in the recursive snark to prove and verify the circuit.
    num_fold_steps: usize,
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> ChunkCircuitInner<F, C, N>
    for InnerCircuit<F, C, N>
{
    fn new(intermediate_steps_input: &[F]) -> anyhow::Result<Self, ChunkError> {
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

                Ok(FoldStep::new(
                    C::new(),
                    inputs,
                    N,
                    i,
                    Some(F::from(i as u64 + 1)),
                ))
            })
            .collect::<anyhow::Result<Vec<_>, ChunkError>>()?;

        // As the input represents the generated values by the inner loop, we need to add one more execution to have
        // a complete circuit and a proper accumulator value.
        circuits.push(FoldStep::new(
            C::new(),
            [F::ZERO; N],
            if intermediate_steps_input.len() % N != 0 {
                intermediate_steps_input.len() % N
            } else {
                N
            },
            circuits.len(),
            None,
        ));

        Ok(Self {
            circuits,
            num_fold_steps: (intermediate_steps_input.len() / N)
                + if intermediate_steps_input.len() % N != 0 {
                    2
                } else {
                    1
                },
        })
    }

    fn initial_input(&self) -> Option<&FoldStep<F, C, N>> {
        self.circuits.first()
    }

    fn num_fold_steps(&self) -> usize {
        self.num_fold_steps
    }
}
