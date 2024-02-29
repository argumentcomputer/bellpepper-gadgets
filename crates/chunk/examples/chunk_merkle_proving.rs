use arecibo::supernova::snark::CompressedSNARK;
use arecibo::supernova::{
    NonUniformCircuit, PublicParams, RecursiveSNARK, StepCircuit, TrivialSecondaryCircuit,
};
use arecibo::traits::snark::default_ck_hint;
use arecibo::traits::{CurveCycleEquipped, Dual, Engine};
use bellpepper::gadgets::boolean::Boolean;
use bellpepper::gadgets::multipack::{bytes_to_bits_le, compute_multipacking, pack_bits};
use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_chunk::traits::ChunkStepCircuit;
use bellpepper_chunk::IterationStep;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_keccak::sha3;
use bellpepper_merkle_inclusion::traits::GadgetDigest;
use bellpepper_merkle_inclusion::{conditional_hash, create_gadget_digest_impl, hash_equality};
use ff::{Field, PrimeField, PrimeFieldBits};
use halo2curves::bn256::Bn256;
use sha3::digest::Output;
use sha3::{Digest, Sha3_256};
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

/*****************************************
 * Utilities
 *****************************************/
create_gadget_digest_impl!(Sha3, sha3, 32, Sha3_256);

// Computes the hash of a preimage.
pub fn hash<D: Digest>(data: &[u8]) -> Output<D> {
    let mut hasher = D::new();
    hasher.update(data);

    hasher.finalize()
}

// Reconstructs a hash from a list of field elements.
fn reconstruct_hash<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    elements: &[AllocatedNum<F>],
    bit_size: usize,
) -> Vec<Boolean> {
    // Compute the bit sizes of the field elements
    let mut scalar_bit_sizes: Vec<usize> = (0..bit_size / F::CAPACITY as usize)
        .map(|_| F::CAPACITY as usize)
        .collect();
    // If the bit size is not a multiple of 253, we need to add the remaining bits
    if bit_size % F::CAPACITY as usize != 0 {
        scalar_bit_sizes.push(bit_size % F::CAPACITY as usize)
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
    pub(crate) iteration_steps: Vec<IterationStep<F, C, N>>,
}

impl<F: PrimeField + PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize>
    MerkleChunkCircuit<F, C, N>
{
    fn new(inputs: &[F]) -> Self {
        Self {
            // We expect EqualityCircuit to be called once the last `IterationStep` is done.
            iteration_steps: IterationStep::from_inputs(0, inputs, F::ONE).unwrap(),
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
enum ChunkCircuitSet<F: PrimeField + PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> {
    IterationStep(IterationStepWrapper<F, C, N>),
    CheckEquality(EqualityCircuit<F>),
}

impl<F: PrimeField + PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> StepCircuit<F>
    for ChunkCircuitSet<F, C, N>
{
    fn arity(&self) -> usize {
        match self {
            Self::IterationStep(iteration_step) => iteration_step.inner.arity(),
            Self::CheckEquality(equality_circuit) => equality_circuit.arity(),
        }
    }

    fn circuit_index(&self) -> usize {
        match self {
            Self::IterationStep(iteration_step) => *iteration_step.inner.circuit_index(),
            Self::CheckEquality(equality_circuit) => equality_circuit.circuit_index(),²
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
            Self::CheckEquality(equality_circuit) => equality_circuit.synthesize(cs, pc, z),
        }
    }
}

impl<E1: CurveCycleEquipped, C: ChunkStepCircuit<E1::Scalar>, const N: usize> NonUniformCircuit<E1>
    for MerkleChunkCircuit<E1::Scalar, C, N>
{
    type C1 = ChunkCircuitSet<E1::Scalar, C, N>;
    type C2 = TrivialSecondaryCircuit<<Dual<E1> as Engine>::Scalar>;

    fn num_circuits(&self) -> usize {
        2
    }

    fn primary_circuit(&self, circuit_index: usize) -> Self::C1 {
        match circuit_index {
            0 => self.get_iteration_circuit(0),
            1 => Self::C1::CheckEquality(EqualityCircuit::new()),
            _ => panic!("No circuit found for index {}", circuit_index),
        }
    }

    fn secondary_circuit(&self) -> Self::C2 {
        Default::default()
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct ChunkStep<F: PrimeField> {
    _p: PhantomData<F>,
}

impl<F: PrimeField + PrimeFieldBits> ChunkStepCircuit<F> for ChunkStep<F> {
    fn new() -> Self {
        Self {
            _p: Default::default(),
        }
    }

    // Expected inputs for our circuit. We expect 4 inputs:
    // 1. The first field element of the leaf hash
    // 2. The second field element of the leaf hash
    // 3. The first field element of the root hash
    // 4. The second field element of the root hash
    fn arity() -> usize {
        4
    }

    // In this case z contains the value described above while chunk_in contains the intermediate hashes to continue
    // the computation.
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
        chunk_in: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let boolean = &chunk_in[0]
            .to_bits_le(&mut cs.namespace(|| "get positional bit"))
            .unwrap()[0];

        let mut acc = reconstruct_hash(&mut cs.namespace(|| "reconstruct acc hash"), &z[0..2], 256);

        // The inputs we handle for one inner iterations are multiple of 3.
        for chunk in chunk_in.chunks(3) {
            let sibling = reconstruct_hash(
                &mut cs.namespace(|| "reconstruct_sibling_hash"),
                &chunk[1..3],
                256,
            );

            acc = conditional_hash::<_, _, Sha3>(
                &mut cs.namespace(|| "conditional_hash"),
                &acc,
                &sibling,
                boolean,
            )?;
        }

        let new_acc_f_1 = pack_bits(&mut cs.namespace(|| "pack_bits new_acc 1"), &acc[..253])?;
        let new_acc_f_2 = pack_bits(&mut cs.namespace(|| "pack_bits new_acc 2"), &acc[253..])?;

        let z_out = vec![new_acc_f_1, new_acc_f_2, z[2].clone(), z[3].clone()];

        Ok(z_out)
    }
}

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
        *self.inner.circuit_index()
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        self.inner
            .synthesize(&mut cs.namespace(|| "iteration_step_wrapper"), pc, z)
    }
}

#[derive(Clone, Debug)]
struct EqualityCircuit<F: PrimeField + PrimeFieldBits> {
    _p: PhantomData<F>,
}

impl<F: PrimeField + PrimeFieldBits> EqualityCircuit<F> {
    pub fn new() -> Self {
        Self {
            _p: Default::default(),
        }
    }
}

impl<F: PrimeField + PrimeFieldBits> StepCircuit<F> for EqualityCircuit<F> {
    fn arity(&self) -> usize {
        7
    }

    fn circuit_index(&self) -> usize {
        1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        let acc = reconstruct_hash(&mut cs.namespace(|| "reconstruct acc hash"), &z[0..2], 256);

        let root_hash =
            reconstruct_hash(&mut cs.namespace(|| "reconstruct acc hash"), &z[2..4], 256);

        let confirmed_hash = hash_equality(&mut cs.namespace(|| "hash_equality"), &acc, root_hash)?;

        let confirmed_hash_f_1 =
            pack_bits(&mut cs.namespace(|| "pack_bits"), &confirmed_hash[..253])?;
        let confirmed_hash_f_2 =
            pack_bits(&mut cs.namespace(|| "pack_bits"), &confirmed_hash[253..])?;

        let z_out = vec![
            confirmed_hash_f_1,
            confirmed_hash_f_2,
            z[2].clone(),
            z[3].clone(),
            z[4].clone(),
            z[5].clone(),
            z[6].clone(),
        ];

        Ok((
            Some(AllocatedNum::alloc(
                &mut cs.namespace(|| "no next circut"),
                || Ok(F::ZERO),
            )?),
            z_out,
        ))
    }
}

const NBR_CHUNK_INPUT: usize = 3;

fn main() {
    // produce public parameters
    let start = Instant::now();

    // Leaf and root hashes
    let a_leaf_hash =
        hash::<<Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher>("a".as_bytes());
    let b_leaf_hash =
        hash::<<Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher>("b".as_bytes());
    let c_leaf_hash =
        hash::<<Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher>("c".as_bytes());
    let d_leaf_hash =
        hash::<<Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher>("d".as_bytes());

    let ab_leaf_hash = hash::<<Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher>(
        &[a_leaf_hash, b_leaf_hash].concat(),
    );
    let cd_leaf_hash = hash::<<Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher>(
        &[c_leaf_hash, d_leaf_hash].concat(),
    );

    let abcd_leaf_hash = hash::<<Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher>(
        &[ab_leaf_hash, cd_leaf_hash].concat(),
    );

    // Intermediate hashes
    let intermediate_hashes: Vec<<E1 as Engine>::Scalar> = [a_leaf_hash, cd_leaf_hash]
        .iter()
        .flat_map(|h| compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(h)))
        .collect();
    let mut intermediate_key_hashes = vec![<E1 as Engine>::Scalar::ONE];
    intermediate_key_hashes.append(&mut intermediate_hashes[0..2].to_vec());
    intermediate_key_hashes.push(<E1 as Engine>::Scalar::ZERO);
    intermediate_key_hashes.append(&mut intermediate_hashes[2..4].to_vec());

    //  Primary circuit
    type C1 = MerkleChunkCircuit<
        <E1 as Engine>::Scalar,
        ChunkStep<<E1 as Engine>::Scalar>,
        NBR_CHUNK_INPUT,
    >;
    let chunk_circuit = C1::new(&intermediate_key_hashes[NBR_CHUNK_INPUT..]);

    // Multipacking the leaf and root hashes
    let mut z0_primary =
        compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(&b_leaf_hash));
    let root_fields =
        compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(&abcd_leaf_hash));

    // The accumulator elements are initialized to 0
    z0_primary.append(&mut root_fields.clone());
    z0_primary.append(&mut intermediate_key_hashes[..NBR_CHUNK_INPUT].to_vec());

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

    // We expect nbr_inputs/chunk_value + 1 (post processning circuit) iterations.
    for step in 0..intermediate_key_hashes.len() / NBR_CHUNK_INPUT + 1 {
        let circuit_primary = if step == intermediate_key_hashes.len() / NBR_CHUNK_INPUT {
            // Check equality
            <C1 as NonUniformCircuit<E1>>::primary_circuit(&chunk_circuit, 1)
        } else {
            // Iteration step
            chunk_circuit.get_iteration_circuit(step)
        };

        let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
        assert!(res.is_ok());
        println!(
            "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
            step,
            res.is_ok(),
            start.elapsed()
        );
    }

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
    let res = compressed_snark.verify(&pp, &verifier_key, &z0_primary, &z0_secondary);
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
}
