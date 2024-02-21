use arecibo::supernova::{
    NonUniformCircuit, PublicParams, RecursiveSNARK, StepCircuit, TrivialSecondaryCircuit,
};
use arecibo::traits::snark::default_ck_hint;
use arecibo::traits::{CurveCycleEquipped, Dual, Engine};
use bellpepper::gadgets::boolean::{field_into_boolean_vec_le, Boolean};
use bellpepper::gadgets::multipack::{bytes_to_bits_le, compute_multipacking};
use bellpepper::gadgets::num::AllocatedNum;
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

fn bytes_to_bitvec(bytes: &[u8]) -> Vec<Boolean> {
    let bits = BitVec::<u8, Lsb0>::from_slice(bytes);
    let bits: Vec<Boolean> = bits.iter().map(|b| Boolean::constant(*b)).collect();
    bits
}

fn sha3(preimage: &[u8]) -> [u8; 32] {
    let mut sha3 = Sha3::v256();

    sha3.update(preimage);

    let mut hash = [0u8; 32];
    sha3.finalize(&mut hash);
    hash
}

fn hash_to_field_elements<F: PrimeField + PrimeFieldBits<Repr = [u8; 32]>>(
    hash_bytes: &[u8; 32],
) -> (F, F) {
    // Split the hash into two parts
    let (part1_bytes, part2_bytes) = hash_bytes.split_at(16);

    let part1_bytes_padded = {
        let mut padded = [0u8; 32];
        padded[..16].copy_from_slice(part1_bytes);
        padded
    };

    let part2_bytes_padded = {
        let mut padded = [0u8; 32];
        padded[..16].copy_from_slice(part2_bytes);
        padded
    };

    // Convert each part to field elements
    let part1_fe = F::from_repr(part1_bytes_padded).unwrap();
    let part2_fe = F::from_repr(part2_bytes_padded).unwrap();

    (part1_fe, part2_fe)
}

fn reconstruct_hash<F: PrimeField + PrimeFieldBits<Repr = [u8; 32]>>(
    element1: F,
    element2: F,
) -> Vec<u8> {
    // Convert each field element back to bytes
    // Note: The exact method to do this will depend on your library
    let mut part1_bytes = element1.to_repr();
    let mut part2_bytes = element2.to_repr();

    // Concatenate the two parts
    let mut hash_bytes = [0u8; 32];
    hash_bytes[..16].copy_from_slice(&part1_bytes[..16]);
    hash_bytes[16..].copy_from_slice(&part2_bytes[..16]);

    hash_bytes.to_vec()
}

/*****************************************
 * Circuit
 *****************************************/

struct ChunkCircuit<F: PrimeField + PrimeFieldBits> {
    _p: PhantomData<F>,
}

impl<F: PrimeField + PrimeFieldBits> ChunkCircuit<F> {
    fn new() -> Self {
        Self {
            _p: Default::default(),
        }
    }
}

#[derive(Clone, Debug)]
enum ChunkCircuitSet<F: PrimeField + PrimeFieldBits> {
    Other(PhantomData<F>),
}

impl<F: PrimeField + PrimeFieldBits> StepCircuit<F> for ChunkCircuitSet<F> {
    fn arity(&self) -> usize {
        5
    }

    fn circuit_index(&self) -> usize {
        0
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        let test1 = z
            .get(1)
            .unwrap()
            .to_bits_le(&mut cs.namespace(|| "test"))
            .unwrap();

        let test2 = z
            .get(2)
            .unwrap()
            .to_bits_le(&mut cs.namespace(|| "test"))
            .unwrap();

        // We need to clone each element to avoid moving them, because MyStruct doesn't implement Copy
        let mut result: Vec<Boolean> = Vec::with_capacity(256);

        // Extend the result with clones of the first 253 elements of vec1
        result.extend(test1.into_iter().take(253));

        // Extend the result with clones of the first 3 elements of test2
        result.extend(test2.into_iter().take(3));

        Ok((
            Some(AllocatedNum::alloc(
                cs.namespace(|| "next_circuit"),
                || Ok(F::ZERO),
            )?),
            vec![
                z[0].clone(),
                z[0].clone(),
                z[0].clone(),
                z[0].clone(),
                z[0].clone(),
            ],
        ))
    }
}

impl<E1: CurveCycleEquipped> NonUniformCircuit<E1> for ChunkCircuit<E1::Scalar> {
    type C1 = ChunkCircuitSet<E1::Scalar>;
    type C2 = TrivialSecondaryCircuit<<Dual<E1> as Engine>::Scalar>;

    fn num_circuits(&self) -> usize {
        1
    }

    fn primary_circuit(&self, circuit_index: usize) -> Self::C1 {
        Self::C1::Other(Default::default())
    }

    fn secondary_circuit(&self) -> Self::C2 {
        Default::default()
    }
}

fn main() {
    // produce public parameters
    let start = Instant::now();

    //  Primary circuit
    type C1 = ChunkCircuit<<E1 as Engine>::Scalar>;
    let chunk_circuit = ChunkCircuit::<<E1 as Engine>::Scalar>::new();

    let a_leaf = sha3("a".as_bytes());
    let mut b_leaf = sha3("b".as_bytes());
    let c_leaf = sha3("c".as_bytes());
    let d_leaf = sha3("d".as_bytes());

    let ab_leaf_hash = sha3(&[a_leaf, b_leaf].concat());
    let cd_leaf_hash = sha3(&[c_leaf, d_leaf].concat());

    let abcd_leaf_hash = sha3(&[ab_leaf_hash, cd_leaf_hash].concat());
    let aa = &bytes_to_bits_le(&b_leaf);

    let mut leaf_fields =
        compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(&b_leaf));

    let mut root_fields =
        compute_multipacking::<<E1 as Engine>::Scalar>(&bytes_to_bits_le(&abcd_leaf_hash));

    let mut z0_primary: Vec<<E1 as Engine>::Scalar> = vec![<E1 as Engine>::Scalar::zero()];

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
