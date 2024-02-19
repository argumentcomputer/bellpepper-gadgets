//! Demonstrates how to create an addition accumulator and looping using the Chunk pattern.
use arecibo::traits::circuit::StepCircuit;
use arecibo::{
    provider::{Bn256EngineKZG, GrumpkinEngine},
    traits::{circuit::TrivialCircuit, snark::RelaxedR1CSSNARKTrait, Engine},
    CompressedSNARK, PublicParams, RecursiveSNARK,
};
use bellpepper_chunk::traits::ChunkCircuit;
use bellpepper_chunk::{traits::ChunkStepCircuit, Circuit, FoldStep};
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use flate2::write::ZlibEncoder;
use flate2::Compression;
use halo2curves::bn256::Bn256;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::time::Instant;
use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};
use tracing_texray::TeXRayLayer;

/*******************************************************
 * User side
 *******************************************************/

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

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        self.inner
            .synthesize(&mut cs.namespace(|| "fold_step_wrapper"), z)
    }
}

/// cargo run --release --example a
fn main() {
    let subscriber = Registry::default()
        .with(fmt::layer().pretty())
        .with(EnvFilter::from_default_env())
        .with(TeXRayLayer::new());
    tracing::subscriber::set_global_default(subscriber).unwrap();

    println!("Addition accumulator with a Chunk pattern");
    println!("=========================================================");

    const NUM_ITERS_PER_STEP: usize = 3;

    type E1 = Bn256EngineKZG;
    type E2 = GrumpkinEngine;
    type EE1 = arecibo::provider::hyperkzg::EvaluationEngine<Bn256, E1>;
    type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = arecibo::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
    type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

    type C1 =
        Circuit<<E1 as Engine>::Scalar, ChunkStep<<E1 as Engine>::Scalar>, NUM_ITERS_PER_STEP>;

    let z0_primary = vec![
        <E1 as Engine>::Scalar::zero(),
        <E1 as Engine>::Scalar::zero(),
        <E1 as Engine>::Scalar::zero(),
        <E1 as Engine>::Scalar::zero(),
    ];

    // number of iterations of MinRoot per Nova's recursive step
    let chunk_circuit = C1::new(&[
        <E1 as Engine>::Scalar::one(),
        <E1 as Engine>::Scalar::from(2),
        <E1 as Engine>::Scalar::from(3),
        <E1 as Engine>::Scalar::from(4),
        <E1 as Engine>::Scalar::from(5),
        <E1 as Engine>::Scalar::from(6),
        <E1 as Engine>::Scalar::from(7),
        <E1 as Engine>::Scalar::from(8),
        <E1 as Engine>::Scalar::from(9),
    ])
    .unwrap();

    let circuit_secondary: TrivialCircuit<<E2 as Engine>::Scalar> = TrivialCircuit::default();

    println!("Proving {NUM_ITERS_PER_STEP} iterations of MinRoot per step");

    // produce public parameters
    let start = Instant::now();

    // produce non-deterministic advice
    let inner_circuits = chunk_circuit.circuits();

    let circuits: Vec<
        FoldStepWrapper<
            <E1 as Engine>::Scalar,
            ChunkStep<<E1 as Engine>::Scalar>,
            NUM_ITERS_PER_STEP,
        >,
    > = inner_circuits
        .iter()
        .map(|i| FoldStepWrapper::new(i.clone()))
        .collect();

    println!("Producing public parameters...");
    let pp = PublicParams::<E1>::setup(
        circuits.first().unwrap(),
        &circuit_secondary,
        &*S1::ck_floor(),
        &*S2::ck_floor(),
    );
    println!("PublicParams::setup, took {:?} ", start.elapsed());

    let z0_secondary = vec![<E2 as Engine>::Scalar::zero()];

    // produce a recursive SNARK
    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark: RecursiveSNARK<E1> = RecursiveSNARK::<E1>::new(
        &pp,
        circuits.first().unwrap(),
        &circuit_secondary,
        &z0_primary,
        &z0_secondary,
    )
    .unwrap();

    for (i, circuit_primary) in circuits.iter().enumerate() {
        let start = Instant::now();

        let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
        assert!(res.is_ok());
        println!(
            "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
            i,
            res.is_ok(),
            start.elapsed()
        );
    }

    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let start = Instant::now();
    let res = recursive_snark.verify(
        &pp,
        chunk_circuit.num_fold_steps(),
        &z0_primary,
        &z0_secondary,
    );
    println!(
        "RecursiveSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    let (z_out, _) = res.unwrap();
    println!("Calculated sum: {:?}", z_out.get(0).unwrap());
    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with multilinear KZG...");
    let (pk, vk) = CompressedSNARK::<_, S1, S2>::setup(&pp).unwrap();

    let start = Instant::now();
    let res = CompressedSNARK::<_, S1, S2>::prove(&pp, &pk, &recursive_snark);
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
    let res = compressed_snark.verify(
        &vk,
        chunk_circuit.num_fold_steps(),
        &z0_primary,
        &z0_secondary,
    );
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
}
