use arecibo::provider::Bn256EngineKZG;
use arecibo::supernova::{NonUniformCircuit, StepCircuit, TrivialSecondaryCircuit};
use arecibo::traits::{CurveCycleEquipped, Dual, Engine};
use bellpepper_chunk::traits::{ChunkCircuitInner, ChunkStepCircuit};
use bellpepper_chunk::{FoldStep, InnerCircuit};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use paste::paste;
use std::marker::PhantomData;

// Used to instantiate our utility
#[derive(Clone, Eq, PartialEq, Debug)]
struct ChunkStep<F: PrimeField> {
    _p: PhantomData<F>,
}

impl<F: PrimeField> ChunkStepCircuit<F> for ChunkStep<F> {
    fn new() -> Self {
        Self {
            _p: Default::default(),
        }
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
        chunk_in: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let mut acc = z[0].clone();

        for (i, elem) in chunk_in.iter().enumerate() {
            acc = acc.add(&mut cs.namespace(|| format!("add{i}")), elem)?;
        }

        Ok(vec![acc])
    }
}

// NIVC `StepCircuit`` implementation
#[derive(Clone, Debug)]
pub struct FoldStepWrapper<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    inner: FoldStep<F, C, N>,
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> FoldStepWrapper<F, C, N> {
    pub fn new(fold_step: FoldStep<F, C, N>) -> Self {
        Self { inner: fold_step }
    }
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> StepCircuit<F>
    for FoldStepWrapper<F, C, N>
{
    fn arity(&self) -> usize {
        self.inner.arity()
    }

    fn circuit_index(&self) -> usize {
        *self.inner.step_nbr()
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        let (next_pc, res_inner_synth) =
            self.inner
                .synthesize(&mut cs.namespace(|| "fold_step_wrapper"), pc, z)?;

        Ok((next_pc, res_inner_synth))
    }
}

// NIVC `NonUniformCircuit` implementation
pub struct ChunkCircuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    inner: InnerCircuit<F, C, N>,
}

#[derive(Clone, Debug)]
pub enum ChunkCircuitSet<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    IterStep(FoldStepWrapper<F, C, N>),
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> StepCircuit<F>
    for ChunkCircuitSet<F, C, N>
{
    fn arity(&self) -> usize {
        match self {
            Self::IterStep(fold_step) => fold_step.inner.arity(),
        }
    }

    fn circuit_index(&self) -> usize {
        match self {
            Self::IterStep(fold_step) => *fold_step.inner.step_nbr(),
        }
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        match self {
            Self::IterStep(fold_step) => fold_step.synthesize(cs, pc, z),
        }
    }
}

impl<E1: CurveCycleEquipped, C: ChunkStepCircuit<E1::Scalar>, const N: usize> NonUniformCircuit<E1>
    for ChunkCircuit<E1::Scalar, C, N>
{
    type C1 = ChunkCircuitSet<E1::Scalar, C, N>;
    type C2 = TrivialSecondaryCircuit<<Dual<E1> as Engine>::Scalar>;

    fn num_circuits(&self) -> usize {
        self.inner.num_fold_steps()
    }

    fn primary_circuit(&self, circuit_index: usize) -> Self::C1 {
        if let Some(fold_step) = self.inner.circuits().get(circuit_index) {
            return Self::C1::IterStep(FoldStepWrapper::new(fold_step.clone()));
        }
        unreachable!()
    }

    fn secondary_circuit(&self) -> Self::C2 {
        Default::default()
    }
}

fn verify_chunk_circuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize>() {
    let test_inputs = vec![F::ONE; 18];

    let expected = (test_inputs.len() / N) + if test_inputs.len() % N != 0 { 2 } else { 1 };

    let circuit = InnerCircuit::<F, C, N>::new(&test_inputs).unwrap();

    let actual = circuit.num_fold_steps();

    assert_eq!(
        &expected, &actual,
        "Expected number of folding steps to be {}, got {}",
        expected, actual
    );

    let mut expected_first_chunk = [F::ZERO; N];

    for i in 0..N {
        if i < test_inputs.len() {
            expected_first_chunk[i] = test_inputs[i];
        }
    }

    let actual_init = circuit.initial_input().unwrap();
    let expected_init =
        FoldStep::<F, C, N>::new(C::new(), expected_first_chunk, N, 0, Some(F::ONE));

    assert_eq!(
        *actual_init, expected_init,
        "Expected initial input to be {:?}, got {:?}",
        expected_init, actual_init
    );

    let actual_circuits = circuit.circuits();

    for (i, actual_circuit) in actual_circuits.iter().enumerate() {
        assert_eq!(
            &i,
            actual_circuit.step_nbr(),
            "Expected inner step nbr to be {:?}, got {:?}",
            i,
            actual_circuit.step_nbr()
        );
    }
}

macro_rules! generate_tests_fold_step_nbr {
    ($($n:expr),*) => {
        $(
            paste! {
                #[test]
                fn [<test_circuit_fold_step_ $n>]() {
                    verify_chunk_circuit::<<Bn256EngineKZG as Engine>::Scalar, ChunkStep<<Bn256EngineKZG as Engine>::Scalar>, { $n }>();
                }
            }
        )*
    };
}

generate_tests_fold_step_nbr!(2, 3, 6, 7, 9, 14, 20);
