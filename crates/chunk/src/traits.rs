use crate::error::ChunkError;
use crate::FoldStep;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

pub trait ChunkStepCircuit<F: PrimeField>: Clone + Sync + Send {
    fn new() -> Self;

    fn arity() -> usize;

    fn chunk_synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
        chunk_in: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>;
}

pub trait ChunkCircuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    fn new(z0_primary: &[F], intermediate_steps_input: &[F]) -> anyhow::Result<Self, ChunkError>
    where
        Self: Sized;
    fn initial_input(&self) -> Option<&FoldStep<F, C, N>>;
    fn num_fold_steps(&self) -> usize;
}
