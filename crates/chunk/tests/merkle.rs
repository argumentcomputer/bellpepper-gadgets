use arecibo::supernova::{NonUniformCircuit, StepCircuit, TrivialSecondaryCircuit};
use arecibo::traits::{CurveCycleEquipped, Dual, Engine};
use bellpepper::gadgets::boolean::Boolean;
use bellpepper::gadgets::multipack::{bytes_to_bits_le, compute_multipacking, pack_bits};
use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_chunk::traits::ChunkStepCircuit;
use bellpepper_chunk::IterationStep;
use bellpepper_core::boolean::AllocatedBit;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_keccak::sha3;
use bellpepper_merkle_inclusion::traits::GadgetDigest;
use bellpepper_merkle_inclusion::{conditional_hash, create_gadget_digest_impl, hash_equality};
use ff::{Field, PrimeField, PrimeFieldBits};
use halo2curves::bn256::Bn256;
use itertools::Itertools;
use sha3::digest::Output;
use sha3::{Digest, Sha3_256};
use std::marker::PhantomData;
use std::ops::Sub;

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
fn reconstruct_hash<F: PrimeFieldBits, CS: ConstraintSystem<F>>(
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
            .to_bits_le(&mut cs.namespace(|| format!("elem to bits le {i}")))
            .unwrap();

        result.extend(element.into_iter().take(*bit_to_take));
    }

    result
}

// TODO should live in bellpepper, close to the Boolean struct
pub fn conditionally_select_bool<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Boolean,
    b: &Boolean,
    condition: &Boolean,
) -> Result<Boolean, SynthesisError> {
    let value = if condition.get_value().unwrap_or_default() {
        a.get_value()
    } else {
        b.get_value()
    };

    let result = Boolean::Is(AllocatedBit::alloc(
        &mut cs.namespace(|| "conditional select result"),
        value,
    )?);

    cs.enforce(
        || "conditional select constraint",
        |_| condition.lc(CS::one(), F::ONE),
        |_| a.lc(CS::one(), F::ONE).sub(&b.lc(CS::one(), F::ONE)),
        |_| result.lc(CS::one(), F::ONE).sub(&b.lc(CS::one(), F::ONE)),
    );

    Ok(result)
}

// TODO should live in bellepper, close to the Boolean struct
/// If condition return a otherwise b
pub fn conditionally_select_vec<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &[Boolean],
    b: &[Boolean],
    condition: &Boolean,
) -> Result<Vec<Boolean>, SynthesisError> {
    a.iter()
        .zip_eq(b.iter())
        .enumerate()
        .map(|(i, (a, b))| {
            conditionally_select_bool(cs.namespace(|| format!("select_{i}")), a, b, condition)
        })
        .collect::<Result<Vec<Boolean>, SynthesisError>>()
}

/*****************************************
 * Circuit
 *****************************************/

struct MerkleChunkCircuit<F: PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> {
    pub(crate) iteration_steps: Vec<IterationStep<F, C, N>>,
}

impl<F: PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> MerkleChunkCircuit<F, C, N> {
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
enum ChunkCircuitSet<F: PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> {
    IterationStep(IterationStepWrapper<F, C, N>),
    CheckEquality(EqualityCircuit<F>),
}

impl<F: PrimeFieldBits, C: ChunkStepCircuit<F>, const N: usize> StepCircuit<F>
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
            Self::CheckEquality(equality_circuit) => equality_circuit.circuit_index(),
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

impl<F: PrimeFieldBits> ChunkStepCircuit<F> for ChunkStep<F> {
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
        chunk_in: &[(Boolean, F)],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let mut acc = reconstruct_hash(&mut cs.namespace(|| "reconstruct acc hash"), &z[0..2], 256);

        // The inputs we handle for one inner iterations are multiple of 3.
        for (i, chunk) in chunk_in.chunks(3).enumerate() {
            let positional_bit = Boolean::Is(AllocatedBit::alloc(
                cs.namespace(|| format!("intermediate input {i} alloc boolean")),
                Some(chunk[0].1.to_le_bits()[0]),
            )?);
            let allocated_siblings = chunk[1..3]
                .iter()
                .enumerate()
                .map(|(j, (_, e))| {
                    AllocatedNum::alloc(
                        cs.namespace(|| format!("intermediate input {i} alloc chunk input {j}")),
                        || Ok(*e),
                    )
                    .unwrap()
                })
                .collect::<Vec<AllocatedNum<F>>>();

            let sibling = reconstruct_hash(
                &mut cs.namespace(|| format!("intermediate input {i} reconstruct_sibling_hash")),
                &allocated_siblings,
                256,
            );

            let next_acc = conditional_hash::<_, _, Sha3>(
                &mut cs.namespace(|| format!("intermediate input {i} conditional_hash")),
                &acc,
                &sibling,
                &positional_bit,
            )?;

            acc = conditionally_select_vec(
                cs.namespace(|| format!("intermediate input {i} conditional_select acc")),
                &next_acc,
                &acc,
                &chunk[0].0,
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
struct EqualityCircuit<F: PrimeFieldBits> {
    _p: PhantomData<F>,
}

impl<F: PrimeFieldBits> EqualityCircuit<F> {
    pub fn new() -> Self {
        Self {
            _p: Default::default(),
        }
    }
}

impl<F: PrimeFieldBits> StepCircuit<F> for EqualityCircuit<F> {
    fn arity(&self) -> usize {
        4
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
            reconstruct_hash(&mut cs.namespace(|| "reconstruct root hash"), &z[2..4], 256);

        let confirmed_hash = hash_equality(&mut cs.namespace(|| "hash_equality"), &acc, root_hash)?;

        let confirmed_hash_f_1 = pack_bits(
            &mut cs.namespace(|| "pack_bits confirmed hash 1"),
            &confirmed_hash[..253],
        )?;
        let confirmed_hash_f_2 = pack_bits(
            &mut cs.namespace(|| "pack_bits confirmed hash 2"),
            &confirmed_hash[253..],
        )?;

        let z_out = vec![
            confirmed_hash_f_1,
            confirmed_hash_f_2,
            z[2].clone(),
            z[3].clone(),
        ];

        Ok((
            Some(AllocatedNum::alloc(
                &mut cs.namespace(|| "no next circuit"),
                || Ok(F::ZERO),
            )?),
            z_out,
        ))
    }
}

const NBR_CHUNK_INPUT: usize = 6;

/// This test is meant to test the implementation of the merkle inclusion proof using the chunk pattern. It also test
/// out the correct behavior of the chunk pattern when a specified chunk size is not a multiple of the input size.
#[test]
fn test_merkle_implementation() {
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

    let last_intermediate_hash = hash::<
        <Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher,
    >("another".as_bytes());
    let root_hash = hash::<<Sha3 as GadgetDigest<<E1 as Engine>::Scalar>>::OutOfCircuitHasher>(
        &[abcd_leaf_hash, last_intermediate_hash].concat(),
    );

    // Intermediate hashes
    let intermediate_hashes: Vec<<E1 as Engine>::Scalar> =
        [a_leaf_hash, cd_leaf_hash, last_intermediate_hash]
            .iter()
            .flat_map(|h| compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(h)))
            .collect();
    let mut intermediate_key_hashes = vec![<E1 as Engine>::Scalar::ONE];
    intermediate_key_hashes.append(&mut intermediate_hashes[0..2].to_vec());
    intermediate_key_hashes.push(<E1 as Engine>::Scalar::ZERO);
    intermediate_key_hashes.append(&mut intermediate_hashes[2..4].to_vec());
    intermediate_key_hashes.push(<E1 as Engine>::Scalar::ZERO);
    intermediate_key_hashes.append(&mut intermediate_hashes[4..6].to_vec());

    //  Primary circuit
    type C1 = MerkleChunkCircuit<
        <E1 as Engine>::Scalar,
        ChunkStep<<E1 as Engine>::Scalar>,
        NBR_CHUNK_INPUT,
    >;

    let chunk_circuit = C1::new(&intermediate_key_hashes);

    // Multipacking the leaf and root hashes
    let mut z0_primary =
        compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(&b_leaf_hash));
    // Expected root hash.
    z0_primary.append(&mut compute_multipacking::<<E1 as Engine>::Scalar>(
        &bytes_to_bits_le(&root_hash),
    ));

    let mut cs = TestConstraintSystem::<<E1 as Engine>::Scalar>::new();

    let z0_primary = z0_primary
        .iter()
        .enumerate()
        .map(|(i, e)| {
            AllocatedNum::alloc(&mut cs.namespace(|| format!("alloc z0 {i}")), || Ok(*e)).unwrap()
        })
        .collect::<Vec<_>>();

    let (_, z1) = chunk_circuit
        .get_iteration_circuit(0)
        .synthesize(&mut cs.namespace(|| "step 0"), None, &z0_primary)
        .unwrap();
    assert!(cs.is_satisfied());
    let (_, z2) = chunk_circuit
        .get_iteration_circuit(1)
        .synthesize(&mut cs.namespace(|| "step 1"), None, &z1)
        .unwrap();
    assert!(cs.is_satisfied());
    let (_, _) = <C1 as NonUniformCircuit<E1>>::primary_circuit(&chunk_circuit, 1)
        .synthesize(&mut cs.namespace(|| "step 2"), None, &z2)
        .unwrap();
    assert!(cs.is_satisfied());
}
