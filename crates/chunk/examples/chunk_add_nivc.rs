use arecibo::supernova::snark::CompressedSNARK;
use arecibo::supernova::{
    NonUniformCircuit, PublicParams, RecursiveSNARK, StepCircuit, TrivialSecondaryCircuit,
};
use arecibo::traits::snark::default_ck_hint;
use arecibo::traits::{CurveCycleEquipped, Dual, Engine};
use bellpepper_chunk::traits::ChunkStepCircuit;
use bellpepper_chunk::IterationStep;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use halo2curves::bn256::Bn256;
use std::marker::PhantomData;
use std::time::Instant;

pub type E1 = arecibo::provider::Bn256EngineKZG;
pub type E2 = arecibo::provider::GrumpkinEngine;
pub type EE1 = arecibo::provider::hyperkzg::EvaluationEngine<Bn256, E1>;
pub type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
// SNARKs without computation commitments
pub type S1 = arecibo::spartan::batched::BatchedRelaxedR1CSSNARK<E1, EE1>;
pub type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;
// SNARKs with computation commitments
pub type SS1 = arecibo::spartan::batched_ppsnark::BatchedRelaxedR1CSSNARK<E1, EE1>;
pub type SS2 = arecibo::spartan::ppsnark::RelaxedR1CSSNARK<E2, EE2>;

/*******************************************************
 * User side
 *******************************************************/

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
struct IterationStepWrapper<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    inner: IterationStep<F, C, N>,
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> IterationStepWrapper<F, C, N> {
    pub fn new(iteration_step: IterationStep<F, C, N>) -> Self {
        Self {
            inner: iteration_step,
        }
    }
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> StepCircuit<F>
    for IterationStepWrapper<F, C, N>
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
                .synthesize(&mut cs.namespace(|| "iteration_step_wrapper"), pc, z)?;

        Ok((next_pc, res_inner_synth))
    }
}

// NIVC `NonUniformCircuit` implementation
struct ChunkCircuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    iteration_steps: Vec<IterationStep<F, C, N>>,
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> ChunkCircuit<F, C, N> {
    pub fn new(inputs: &[F]) -> Self {
        Self {
            iteration_steps: IterationStep::from_inputs(0, inputs, F::ZERO).unwrap(),
        }
    }

    fn get_iteration_step(&self, step: usize) -> IterationStep<F, C, N> {
        self.iteration_steps[step].clone()
    }

    fn get_iteration_circuit(&self, step: usize) -> ChunkCircuitSet<F, C, N> {
        ChunkCircuitSet::IterationStep(IterationStepWrapper::new(self.get_iteration_step(step)))
    }
}

#[derive(Clone, Debug)]
enum ChunkCircuitSet<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    IterationStep(IterationStepWrapper<F, C, N>),
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> StepCircuit<F>
    for ChunkCircuitSet<F, C, N>
{
    fn arity(&self) -> usize {
        match self {
            Self::IterationStep(iteration_step) => iteration_step.inner.arity(),
        }
    }

    fn circuit_index(&self) -> usize {
        match self {
            Self::IterationStep(iteration_step) => *iteration_step.inner.circuit_index(),
        }
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        match self {
            Self::IterationStep(iteration_step) => iteration_step.synthesize(cs, pc, z),
        }
    }
}

impl<E1: CurveCycleEquipped, C: ChunkStepCircuit<E1::Scalar>, const N: usize> NonUniformCircuit<E1>
    for ChunkCircuit<E1::Scalar, C, N>
{
    type C1 = ChunkCircuitSet<E1::Scalar, C, N>;
    type C2 = TrivialSecondaryCircuit<<Dual<E1> as Engine>::Scalar>;

    fn num_circuits(&self) -> usize {
        1
    }

    fn primary_circuit(&self, circuit_index: usize) -> Self::C1 {
        match circuit_index {
            0 => {
                Self::C1::IterationStep(IterationStepWrapper::new(self.iteration_steps[0].clone()))
            }
            _ => panic!("No circuit found for index {}", circuit_index),
        }
    }

    fn secondary_circuit(&self) -> Self::C2 {
        Default::default()
    }
}

fn main() {
    const NUM_ITERS_PER_STEP: usize = 3;

    type C1 =
        ChunkCircuit<<E1 as Engine>::Scalar, ChunkStep<<E1 as Engine>::Scalar>, NUM_ITERS_PER_STEP>;

    println!("NIVC addition accumulator with a Chunk pattern");
    println!("=========================================================");

    let inputs = vec![
        <E1 as Engine>::Scalar::zero(),
        <E1 as Engine>::Scalar::one(),
        <E1 as Engine>::Scalar::from(2),
        <E1 as Engine>::Scalar::from(3),
        <E1 as Engine>::Scalar::from(4),
        <E1 as Engine>::Scalar::from(5),
        <E1 as Engine>::Scalar::from(6),
        <E1 as Engine>::Scalar::from(7),
        <E1 as Engine>::Scalar::from(8),
        <E1 as Engine>::Scalar::from(9),
        <E1 as Engine>::Scalar::from(10),
    ];

    let z0_primary = &[
        &[<E1 as Engine>::Scalar::zero()],
        &inputs[..NUM_ITERS_PER_STEP],
    ]
    .concat();

    let intermediate_inputs = &inputs[NUM_ITERS_PER_STEP..];

    // Different instantiations of circuit for each of the nova fold steps
    let chunk_circuit = C1::new(intermediate_inputs);

    let circuit_secondary = <C1 as NonUniformCircuit<E1>>::secondary_circuit(&chunk_circuit);

    let z0_secondary = vec![<Dual<E1> as Engine>::Scalar::ZERO];

    println!(
        "Proving {} iterations of Chunk per step",
        inputs.len() / NUM_ITERS_PER_STEP + 1
    );

    // produce public parameters
    let start = Instant::now();

    println!("Producing public parameters...");
    // produce public parameters
    let pp = PublicParams::<E1>::setup(&chunk_circuit, &*default_ck_hint(), &*default_ck_hint());
    println!("PublicParams::setup, took {:?} ", start.elapsed());

    // produce a recursive SNARK
    let circuit_primary = <C1 as NonUniformCircuit<E1>>::primary_circuit(&chunk_circuit, 0);

    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark = RecursiveSNARK::<E1>::new(
        &pp,
        &chunk_circuit,
        &circuit_primary,
        &circuit_secondary,
        z0_primary,
        &z0_secondary,
    )
    .unwrap();

    let start = Instant::now();

    // We +1 the number of folding steps to account for the modulo of intermediate_inputs.len() by NUM_ITERS_PER_STEP being != 0
    for step in 0..inputs.len() / NUM_ITERS_PER_STEP + 1 {
        let circuit_primary = chunk_circuit.get_iteration_circuit(step);
        let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
        assert!(res.is_ok());
        println!(
            "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
            step,
            res.is_ok(),
            start.elapsed()
        );
    }
    assert_eq!(
        &<E1 as Engine>::Scalar::from(55),
        recursive_snark.zi_primary().first().unwrap()
    );
    println!(
        "Calculated sum: {:?}",
        recursive_snark.zi_primary().first().unwrap()
    );

    println!("Generating a CompressedSNARK...");
    let (prover_key, verifier_key) = CompressedSNARK::<_, S1, S2>::setup(&pp).unwrap();

    let start = Instant::now();
    let res = CompressedSNARK::<_, S1, S2>::prove(&pp, &prover_key, &recursive_snark);
    println!(
        "CompressedSNARK::prove: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&pp, &verifier_key, z0_primary, &z0_secondary);
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
}
