use bellpepper_core::boolean::Boolean;
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
    /// * `chunk_in` - A pair representing (input validity, input value) for each input.
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
        chunk_in: &[(Boolean, F)],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>;
}
