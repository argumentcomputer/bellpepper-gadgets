use std::ops::{Div, Rem};

use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigInt;
use num_traits::Zero;

use crate::field_element::EmulatedLimbs;
use crate::util::{bigint_to_scalar, decompose};
use crate::{field_element::EmulatedFieldElement, field_element::EmulatedFieldParams};

impl<F, P> EmulatedFieldElement<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    /// Computes the remainder modulo the field modulus
    pub(crate) fn compute_rem<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a_int: BigInt = self.into();
        let p = P::modulus();
        let r_int = a_int.rem(p);
        let r_value = Self::from(&r_int);

        let res_limbs =
            r_value.allocate_limbs(&mut cs.namespace(|| "allocate from remainder value"))?;

        let res = Self::pack_limbs(
            &mut cs.namespace(|| "enforce bitwidths on remainder"),
            res_limbs,
            true,
        )?;
        Ok(res)
    }

    /// Computes the quotient
    pub(crate) fn compute_quotient<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // TODO: Check the need for the "+ 1"
        let num_res_limbs = (self.len()*P::bits_per_limb() + self.overflow + 1
            - (P::modulus().bits() as usize)    // Deduct the modulus bit size
            + P::bits_per_limb() - 1) /         // This term is to round up to next integer
            P::bits_per_limb();

        let a_int: BigInt = self.into();
        let p = P::modulus();
        let k_int = a_int.div(p);
        let k_int_limbs = decompose(&k_int, P::bits_per_limb(), num_res_limbs)?;

        let res_limb_values: Vec<F> = k_int_limbs
            .into_iter()
            .map(|i| bigint_to_scalar(&i))
            .collect::<Vec<F>>();

        let res_limbs = EmulatedLimbs::<F>::allocate_limbs(
            &mut cs.namespace(|| "allocate from quotient value"),
            &res_limb_values,
        )?;

        let res = Self::pack_limbs(
            &mut cs.namespace(|| "enforce bitwidths on quotient"),
            res_limbs,
            false,
        )?;
        Ok(res)
    }

    /// Computes the multiplicative inverse
    pub(crate) fn compute_inverse<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut a_int: BigInt = self.into();
        let p = P::modulus();
        a_int = a_int.rem(&p);
        if a_int.is_zero() {
            eprintln!("Inverse of zero element cannot be calculated");
            return Err(SynthesisError::DivisionByZero);
        }
        let p_minus_2 = &p - BigInt::from(2);
        // a^(p-1) = 1 mod p for non-zero a. So a^(-1) = a^(p-2)
        let a_inv_int = a_int.modpow(&p_minus_2, &p);
        let a_inv_value = Self::from(&a_inv_int);

        let a_inv_limbs =
            a_inv_value.allocate_limbs(&mut cs.namespace(|| "allocate from inverse value"))?;

        let a_inv = Self::pack_limbs(
            &mut cs.namespace(|| "enforce bitwidths on inverse"),
            a_inv_limbs,
            true,
        )?;

        Ok(a_inv)
    }

    /// Computes the ratio modulo the field modulus
    pub(crate) fn compute_ratio<CS>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let numer_int: BigInt = self.into();
        let mut denom_int: BigInt = other.into();
        let p = P::modulus();
        denom_int = denom_int.rem(&p);
        if denom_int.is_zero() {
            eprintln!("Inverse of zero element cannot be calculated");
            return Err(SynthesisError::DivisionByZero);
        }
        let p_minus_2 = &p - BigInt::from(2);
        // a^(p-1) = 1 mod p for non-zero a. So a^(-1) = a^(p-2)
        let denom_inv_int = denom_int.modpow(&p_minus_2, &p);
        let ratio_int = (numer_int * denom_inv_int).rem(&p);

        let ratio_value = Self::from(&ratio_int);

        let ratio_limbs =
            ratio_value.allocate_limbs(&mut cs.namespace(|| "allocate from ratio value"))?;

        let ratio = Self::pack_limbs(
            &mut cs.namespace(|| "enforce bitwidths on ratio"),
            ratio_limbs,
            true,
        )?;

        Ok(ratio)
    }
}
