use std::array::TryFromSliceError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ChunkError {
    #[error("For now we only support the number of inputs being a multiple of the number of steps in the circuit. Got {0} inputs for {1} steps.")]
    InvalidInputLength(usize, usize),
    #[error("Could not divide given inputs for the chunk pattern. Got: {source}")]
    DivisionError {
        #[source]
        source: TryFromSliceError,
    },
}
