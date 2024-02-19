use arecibo::supernova::snark::CompressedSNARK;
use arecibo::supernova::{
    NonUniformCircuit, PublicParams, RecursiveSNARK, StepCircuit, TrivialSecondaryCircuit,
};
use arecibo::traits::snark::default_ck_hint;
use arecibo::traits::{CurveCycleEquipped, Dual, Engine};
use bellpepper_chunk::traits::{ChunkCircuitInner, ChunkStepCircuit};
use bellpepper_chunk::{FoldStep, InnerCircuit};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use flate2::write::ZlibEncoder;
use flate2::Compression;
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

    fn chunk_synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
        chunk_in: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let mut acc = z[0].clone();

        for (i, elem) in chunk_in.iter().enumerate() {
            // TODO i is not what we want here. Should be fold_step + i
            acc = acc.add(&mut cs.namespace(|| format!("add{i}")), &elem)?;
        }

        Ok(vec![acc])
    }
}

// NIVC `StepCircuit`` implementation
#[derive(Clone, Debug)]
struct FoldStepWrapper<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
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
struct ChunkCircuit<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
    inner: InnerCircuit<F, C, N>,
}

impl<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> ChunkCircuit<F, C, N> {
    pub fn new(inner: InnerCircuit<F, C, N>) -> Self {
        Self { inner }
    }
}

#[derive(Clone, Debug)]
enum ChunkCircuitSet<F: PrimeField, C: ChunkStepCircuit<F>, const N: usize> {
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
        match circuit_index {
            _ => {
                if let Some(fold_step) = self.inner.circuits().get(circuit_index) {
                    return Self::C1::IterStep(FoldStepWrapper::new(fold_step.clone()));
                }
                unreachable!()
            }
        }
    }

    fn secondary_circuit(&self) -> Self::C2 {
        Default::default()
    }
}

fn main() {
    const NUM_ITERS_PER_STEP: usize = 3;

    type Inner =
        InnerCircuit<<E1 as Engine>::Scalar, ChunkStep<<E1 as Engine>::Scalar>, NUM_ITERS_PER_STEP>;
    type C1 =
        ChunkCircuit<<E1 as Engine>::Scalar, ChunkStep<<E1 as Engine>::Scalar>, NUM_ITERS_PER_STEP>;

    println!("IVC addition accumulator with a Chunk pattern");
    println!("=========================================================");

    let z0_primary = vec![
        <E1 as Engine>::Scalar::zero(),
        <E1 as Engine>::Scalar::zero(),
        <E1 as Engine>::Scalar::zero(),
        <E1 as Engine>::Scalar::zero(),
    ];

    // number of iterations of MinRoot per Nova's recursive step
    let inner_chunk_circuit = Inner::new(&[
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
    ])
    .unwrap();

    let chunk_circuit = C1::new(inner_chunk_circuit);

    let circuit_secondary = <C1 as NonUniformCircuit<E1>>::secondary_circuit(&chunk_circuit);

    // produce non-deterministic hint
    assert_eq!(
        <C1 as NonUniformCircuit<E1>>::num_circuits(&chunk_circuit),
        5
    );

    let z0_secondary = vec![<Dual<E1> as Engine>::Scalar::ZERO];

    println!(
        "Proving {} iterations of Chunk per step",
        <C1 as NonUniformCircuit<E1>>::num_circuits(&chunk_circuit)
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
        &z0_primary,
        &z0_secondary,
    )
    .unwrap();

    for step in 0..<C1 as NonUniformCircuit<E1>>::num_circuits(&chunk_circuit) {
        let start = Instant::now();

        let circuit_primary =
            <ChunkCircuit<
                <E1 as Engine>::Scalar,
                ChunkStep<<E1 as Engine>::Scalar>,
                NUM_ITERS_PER_STEP,
            > as NonUniformCircuit<E1>>::primary_circuit(&chunk_circuit, step);

        let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
        assert!(res.is_ok());
        println!(
            "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
            step,
            res.is_ok(),
            start.elapsed()
        );

        let start = Instant::now();

        let res = recursive_snark.verify(&pp, &z0_primary, &z0_secondary);
        assert!(res.is_ok());
        println!(
            "RecursiveSNARK::verify {}: {:?}, took {:?} ",
            step,
            res.is_ok(),
            start.elapsed()
        );
    }
    println!(
        "Calculated sum: {:?}",
        recursive_snark.zi_primary().get(0).unwrap()
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

    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
    let compressed_snark_encoded = encoder.finish().unwrap();
    println!(
        "CompressedSNARK::len {:?} bytes",
        compressed_snark_encoded.len()
    );

    // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&pp, &verifier_key, &z0_primary, &z0_secondary);
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
}
