use arecibo::provider::Bn256EngineKZG;
use arecibo::traits::Engine;
use bellpepper_chunk::traits::ChunkStepCircuit;
use bellpepper_chunk::IterationStep;
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

fn verify_chunk_circuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize>() {
    let test_inputs = vec![F::ONE; 18];

    let expected = (test_inputs.len() / N) + if test_inputs.len() % N != 0 { 2 } else { 1 };

    let circuits = IterationStep::<F, C, N>::from_inputs(0, &test_inputs, F::ONE).unwrap();

    let actual = circuits.len();

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

    let actual_first = &circuits[0];
    let expected_first =
        IterationStep::<F, C, N>::new(0, C::new(), expected_first_chunk, N, 0, F::ZERO);

    assert_eq!(
        actual_first, &expected_first,
        "Expected first iteration step to be {:?}, got {:?}",
        expected_first, actual_first
    );

    for (i, circuit) in circuits[..circuits.len() - 1].iter().enumerate() {
        assert_eq!(
            &i,
            circuit.step_nbr(),
            "Expected inner step nbr to be {:?}, got {:?}",
            i,
            circuit.step_nbr()
        );

        if i == circuits.len() - 1 {
            assert_eq!(
                &F::ONE,
                circuit.next_pc(),
                "Expected inner step nbr to be {:?}, got {:?}",
                F::from(1),
                circuit.next_pc()
            );
        } else {
            assert_eq!(
                &F::ZERO,
                circuit.next_pc(),
                "Expected inner step nbr to be {:?}, got {:?}",
                F::from(0),
                circuit.next_pc()
            );
        }
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
