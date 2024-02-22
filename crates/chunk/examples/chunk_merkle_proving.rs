use arecibo::supernova::{
    NonUniformCircuit, PublicParams, RecursiveSNARK, StepCircuit, TrivialSecondaryCircuit,
};
use arecibo::traits::snark::default_ck_hint;
use arecibo::traits::{CurveCycleEquipped, Dual, Engine};
use bellpepper::gadgets::boolean::{field_into_boolean_vec_le, Boolean};
use bellpepper::gadgets::multipack::{bytes_to_bits_le, compute_multipacking};
use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_chunk::traits::{ChunkCircuitInner, ChunkStepCircuit};
use bellpepper_chunk::{FoldStep, InnerCircuit};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bitvec::order::Lsb0;
use bitvec::prelude::BitVec;
use ff::{Field, PrimeField, PrimeFieldBits};
use halo2curves::bn256::Bn256;
use std::marker::PhantomData;
use std::time::Instant;
use tiny_keccak::{Hasher, Sha3};

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

/*****************************************
 * Utilities
 *****************************************/
// Computes the sha3 hash of a preimage.
fn sha3(preimage: &[u8]) -> [u8; 32] {
    let mut sha3 = Sha3::v256();

    sha3.update(preimage);

    let mut hash = [0u8; 32];
    sha3.finalize(&mut hash);
    hash
}

// Reconstructs a hash from a list of field elements.
fn reconstruct_hash<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    elements: &[AllocatedNum<F>],
    bit_size: usize,
) -> Vec<Boolean> {
    // Compute the bit sizes of the field elements
    let mut scalar_bit_sizes: Vec<usize> = (0..bit_size / F::CAPACITY as usize)
        .map(|i| F::CAPACITY as usize)
        .collect();
    // If the bit size is not a multiple of 253, we need to add the remaining bits
    if bit_size % F::CAPACITY != 0 {
        scalar_bit_sizes.push(bit_size % F::CAPACITY)
    }

    assert_eq!(
        elements.len(),
        scalar_bit_sizes.len(),
        "Got {} elements to reconstruct hash, expected {}",
        elements.len(),
        scalar_bit_sizes.len()
    );

    let mut result: Vec<Boolean> = vec![];

    // For each field element, take the first `bit_size` bits
    for (i, bit_to_take) in scalar_bit_sizes.iter().enumerate() {
        let element = elements[i]
            .to_bits_le(&mut cs.namespace(|| "test"))
            .unwrap();

        result.extend(element.into_iter().take(*bit_to_take));
    }

    result
}

/*****************************************
 * Circuit
 *****************************************/

struct MerkleChunkCircuit<F: PrimeField + PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> {
    inner: InnerCircuit<F, C, N>,
}

impl<F: PrimeField + PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize>
    MerkleChunkCircuit<F, C, N>
{
    fn new(leaf_key: Vec<Boolean>, sibling_hashes: Vec<Boolean>) -> Self {
        Self {
            inner: InnerCircuit::new(&[]).unwrap(),
        }
    }
}

#[derive(Clone, Debug)]
enum ChunkCircuitSet<F: PrimeField + PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> {
    IterStep(FoldStepWrapper<F, C, N>),
}

impl<F: PrimeField + PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> StepCircuit<F>
    for ChunkCircuitSet<F, C, N>
{
    fn arity(&self) -> usize {
        6
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
    for MerkleChunkCircuit<E1::Scalar, C, N>
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
        panic!("No circuit found for index {}", circuit_index)
    }

    fn secondary_circuit(&self) -> Self::C2 {
        Default::default()
    }
}

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

    // Expected inputs for our circuit. We expect 6 inputs:
    // 1. The first field element of the accumulator hash
    // 2. The second field element of the accumulator hash
    // 3. The first field element of the leaf hash
    // 4. The second field element of the leaf hash
    // 5. The first field element of the root hash
    // 6. The second field element of the root hash
    fn arity() -> usize {
        6
    }

    // In this case z contains the value described above while chunk_in contains the intermediate hashes to continue
    // the computation.
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _pc: Option<&bellpepper_core::num::AllocatedNum<F>>,
        z: &[bellpepper_core::num::AllocatedNum<F>],
        chunk_in: &[bellpepper_core::num::AllocatedNum<F>],
    ) -> Result<Vec<bellpepper_core::num::AllocatedNum<F>>, SynthesisError> {
        todo!()
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

fn main() {
    // produce public parameters
    let start = Instant::now();

    //  Primary circuit
    type C1 = MerkleChunkCircuit<<E1 as Engine>::Scalar, ChunkStep<<E1 as Engine>::Scalar>, 1>;
    let chunk_circuit = C1::new(vec![], vec![]);

    // Leaf and root hashes
    let a_leaf = sha3("a".as_bytes());
    let mut b_leaf = sha3("b".as_bytes());
    let c_leaf = sha3("c".as_bytes());
    let d_leaf = sha3("d".as_bytes());

    let ab_leaf_hash = sha3(&[a_leaf, b_leaf].concat());
    let cd_leaf_hash = sha3(&[c_leaf, d_leaf].concat());

    let abcd_leaf_hash = sha3(&[ab_leaf_hash, cd_leaf_hash].concat());
    let aa = &bytes_to_bits_le(&b_leaf);

    // Multipacking the leaf and root hashes
    let mut leaf_fields =
        compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(&b_leaf));
    let mut root_fields =
        compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(&abcd_leaf_hash));

    // The accumulator elements are initialized to 0
    let mut z0_primary: Vec<<E1 as Engine>::Scalar> = vec![
        <E1 as Engine>::Scalar::zero(),
        <E1 as Engine>::Scalar::zero(),
    ];

    z0_primary.append(&mut leaf_fields.clone());
    z0_primary.append(&mut root_fields.clone());

    let circuit_primary = <C1 as NonUniformCircuit<E1>>::primary_circuit(&chunk_circuit, 0);

    // Secondary circuit
    let circuit_secondary = <C1 as NonUniformCircuit<E1>>::secondary_circuit(&chunk_circuit);
    let z0_secondary = vec![<Dual<E1> as Engine>::Scalar::ZERO];

    println!("Producing public parameters...");
    // produce public parameters
    let pp = PublicParams::<E1>::setup(&chunk_circuit, &*default_ck_hint(), &*default_ck_hint());
    println!("PublicParams::setup, took {:?} ", start.elapsed());

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

    let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
    dbg!(res.is_ok());
}
