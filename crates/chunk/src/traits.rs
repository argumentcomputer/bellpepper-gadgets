use crate::error::ChunkError;
use crate::FoldStep;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use std::fmt::Debug;

/// `ChunkStepCircuit` is the trait used to interface with one step in a loop of a `ChunkCircuit`.
pub trait ChunkStepCircuit<F: PrimeField>: Clone + Sync + Send + Debug + PartialEq + Eq {
    /// `new` should return a new instance of the step circuit.
    fn new() -> Self;

    /// `arity` must return the number of inputs or outputs of each step.
    fn arity() -> usize {
        1
    }

    /// `synthesize` must be the method that performs the computation for a given step.
    ///
    /// # Arguments
    /// * `cs` - The constraint system to which the circuit is being added.
    /// * `pc` - The program counter value for the current step.
    /// * `z` - The accumulator value for the current step.
    /// * `chunk_in` - The input values for the current step (which are the output values from the previous step).
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
        chunk_in: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>;
}

/// `ChunkCircuit` is the trait used to interface with a circuit that is composed of a loop of steps.
pub trait ChunkCircuitInner<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    /// `new` must return a new instance of the chunk circuit.
    /// # Arguments
    /// * `intermediate_steps_input` - The intermediate input values for each of the step circuits.
    /// * `post_processing_circuit` - The post processing circuit to be used after the loop of steps.
    ///
    /// # Note
    ///
    /// As `intermediate_steps_input` represents the input values for each of the step circuits, there is currently a need
    /// to generate one last `FoldStep` instance to represent the last step in the circuit.
    fn new(
        intermediate_steps_input: &[F],
        post_processing_circuit: Option<F>,
    ) -> anyhow::Result<Self, ChunkError>
    where
        Self: Sized;
    /// `initial_input` must return the first circuit to be proven/verified.
    fn initial_input(&self) -> Option<&FoldStep<F, C, N>>;
    /// `num_fold_steps` must return the number of recursive snark step necessary to prove and verify the circuit.
    fn num_fold_steps(&self) -> usize;
}
