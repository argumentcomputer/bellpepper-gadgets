use arecibo::supernova::{NonUniformCircuit, PublicParams, TrivialSecondaryCircuit};
use arecibo::traits::snark::default_ck_hint;
use arecibo::traits::{CurveCycleEquipped, Dual, Engine};
use ff::PrimeField;
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

struct ChunkCircuit<F: PrimeField> {
    _p: PhantomData<F>,
}

impl<F: PrimeField> ChunkCircuit<F> {
    fn new() -> Self {
        Self {
            _p: Default::default(),
        }
    }
}

impl<E1: CurveCycleEquipped> NonUniformCircuit<E1> for ChunkCircuit<E1::Scalar> {
    type C1 = ();
    type C2 = TrivialSecondaryCircuit<<Dual<E1> as Engine>::Scalar>;

    fn num_circuits(&self) -> usize {
        todo!()
    }

    fn primary_circuit(&self, circuit_index: usize) -> Self::C1 {
        todo!()
    }

    fn secondary_circuit(&self) -> Self::C2 {
        Default::default()
    }
}

fn main() {
    // produce public parameters
    let start = Instant::now();

    let chunk_circuit = ChunkCircuit::<E1::Scalar>::new();

    println!("Producing public parameters...");
    // produce public parameters
    let pp = PublicParams::<E1>::setup(&chunk_circuit, &*default_ck_hint(), &*default_ck_hint());
    println!("PublicParams::setup, took {:?} ", start.elapsed());
}
