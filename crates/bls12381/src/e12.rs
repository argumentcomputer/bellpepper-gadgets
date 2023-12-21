use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::fp12::Fp12 as BlsFp12;
use bls12_381::fp6::Fp6 as BlsFp6;
use ff::{PrimeField, PrimeFieldBits};

use crate::e2::AllocatedE2Element;
use crate::e6::AllocatedE6Element;

#[derive(Clone)]
pub struct AllocatedE12Element<F: PrimeField + PrimeFieldBits> {
    pub(crate) c0: AllocatedE6Element<F>,
    pub(crate) c1: AllocatedE6Element<F>,
}

#[derive(Clone)]
pub struct Torus<F: PrimeField + PrimeFieldBits>(pub AllocatedE6Element<F>);

impl<F> From<&BlsFp12> for AllocatedE12Element<F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &BlsFp12) -> Self {
        let c0 = AllocatedE6Element::<F>::from(&value.c0);
        let c1 = AllocatedE6Element::<F>::from(&value.c1);
        Self { c0, c1 }
    }
}

impl<F> From<&AllocatedE12Element<F>> for BlsFp12
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &AllocatedE12Element<F>) -> Self {
        let c0 = BlsFp6::from(&value.c0);
        let c1 = BlsFp6::from(&value.c1);
        BlsFp12 { c0, c1 }
    }
}

impl<F: PrimeField + PrimeFieldBits> AllocatedE12Element<F> {
    pub fn zero() -> Self {
        Self {
            c0: AllocatedE6Element::zero(),
            c1: AllocatedE6Element::zero(),
        }
    }

    pub fn one() -> Self {
        Self {
            c0: AllocatedE6Element::one(),
            c1: AllocatedE6Element::zero(),
        }
    }

    pub fn alloc_element<CS>(cs: &mut CS, value: &BlsFp12) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 =
            AllocatedE6Element::<F>::alloc_element(&mut cs.namespace(|| "allocate c0"), &value.c0)?;
        let c1 =
            AllocatedE6Element::<F>::alloc_element(&mut cs.namespace(|| "allocate c1"), &value.c1)?;

        Ok(Self { c0, c1 })
    }

    pub fn assert_is_equal<CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        AllocatedE6Element::<F>::assert_is_equal(&mut cs.namespace(|| "c0 =? c0"), &a.c0, &b.c0)?;
        AllocatedE6Element::<F>::assert_is_equal(&mut cs.namespace(|| "c1 =? c1"), &a.c1, &b.c1)?;
        Ok(())
    }

    pub fn reduce<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0_reduced = self.c0.reduce(&mut cs.namespace(|| "c0 mod P"))?;
        let c1_reduced = self.c1.reduce(&mut cs.namespace(|| "c1 mod P"))?;
        Ok(Self {
            c0: c0_reduced,
            c1: c1_reduced,
        })
    }

    pub fn assert_equality_to_constant<CS>(
        &self,
        cs: &mut CS,
        constant: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.c0
            .assert_equality_to_constant(&mut cs.namespace(|| "c0 =? (const) c0"), &constant.c0)?;
        self.c1
            .assert_equality_to_constant(&mut cs.namespace(|| "c1 =? (const) c1"), &constant.c1)?;
        Ok(())
    }

    pub fn alloc_is_zero<CS>(&self, cs: &mut CS) -> Result<AllocatedBit, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z0 = self.c0.alloc_is_zero(&mut cs.namespace(|| "c0 =? 0"))?;
        let z1 = self.c1.alloc_is_zero(&mut cs.namespace(|| "c1 =? 0"))?;

        AllocatedBit::and(&mut cs.namespace(|| "and(z0, z1)"), &z0, &z1)
    }

    pub fn add<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self
            .c0
            .add(&mut cs.namespace(|| "compute c0 + c0"), &value.c0)?;
        let c1 = self
            .c1
            .add(&mut cs.namespace(|| "compute c1 + c1"), &value.c1)?;
        Ok(Self { c0, c1 })
    }

    pub fn sub<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self
            .c0
            .sub(&mut cs.namespace(|| "compute c0 - c0"), &value.c0)?;
        let c1 = self
            .c1
            .sub(&mut cs.namespace(|| "compute c1 - c1"), &value.c1)?;
        Ok(Self { c0, c1 })
    }

    pub fn conjugate<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z1 = self.c1.neg(&mut cs.namespace(|| "conj e12"))?;
        Ok(Self {
            c0: self.c0.clone(),
            c1: z1,
        })
    }

    pub fn mul<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (x, y) = (self, value);
        let mut cs = cs.namespace(|| "compute e12 mul(x,y)");
        let a = x.c0.add(&mut cs.namespace(|| "a <- x.c0 + x.c1"), &x.c1)?;
        let b = y.c0.add(&mut cs.namespace(|| "b <- y.c0 + y.c1"), &y.c1)?;
        let a = a.mul(&mut cs.namespace(|| "a <- a * b"), &b)?;
        let b = x.c0.mul(&mut cs.namespace(|| "b <- x.c0 * y.c0"), &y.c0)?;
        let c = x.c1.mul(&mut cs.namespace(|| "c <- x.c1 * y.c1"), &y.c1)?;
        let z1 = a.sub(&mut cs.namespace(|| "z1 <- a - b"), &b)?;
        let z1 = z1.sub(&mut cs.namespace(|| "z1 <- z1 - c"), &c)?;
        let z0 = c.mul_by_nonresidue(&mut cs.namespace(|| "z0 <- c.mul_by_nonresidue()"))?;
        let z0 = z0.add(&mut cs.namespace(|| "z0 <- z0 + b"), &b)?;

        Ok(Self { c0: z0, c1: z1 })
    }

    pub fn square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self;
        let mut cs = cs.namespace(|| "compute e12 square(x)");
        let c0 = x.c0.sub(&mut cs.namespace(|| "c0 <- x.c0 - x.c1"), &x.c1)?;
        let c3 =
            x.c1.mul_by_nonresidue(&mut cs.namespace(|| "c3 <- x.c1.mul_by_nonresidue()"))?;
        let c3 = c3.neg(&mut cs.namespace(|| "c3 <- c3.neg()"))?;
        let c3 = x.c0.add(&mut cs.namespace(|| "c3 <- x.c0 + c3"), &c3)?;
        let c2 = x.c0.mul(&mut cs.namespace(|| "c2 <- x.c0 * x.c1"), &x.c1)?;
        let c0 = c0.mul(&mut cs.namespace(|| "c0 <- c0 * c3"), &c3)?;
        let c0 = c0.add(&mut cs.namespace(|| "c0 <- c0 + c2"), &c2)?;
        let z1 = c2.double(&mut cs.namespace(|| "z1 <- c2.double()"))?;
        let c2 = c2.mul_by_nonresidue(&mut cs.namespace(|| "c2 <- c2.mul_by_nonresidue()"))?;
        let z0 = c0.add(&mut cs.namespace(|| "z0 <- c0 + c2"), &c2)?;

        Ok(Self { c0: z0, c1: z1 })
    }

    pub fn inverse<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let val = BlsFp12::from(self);
        if val.is_zero().into() {
            eprintln!("Inverse of zero element cannot be calculated");
            return Err(SynthesisError::DivisionByZero);
        }
        let inv = val.invert().unwrap();

        let inv_alloc = Self::alloc_element(&mut cs.namespace(|| "alloc inv"), &inv)?;

        // x*inv = 1
        let prod = inv_alloc.mul(&mut cs.namespace(|| "x*inv"), self)?;

        // CLEANUP: do we need to reduce here (and add the width constraints and etc) or would compute_rem be enough?
        // can't really assert equality to constant here without reducing it mod P, but this has more constraints than
        // just using assert_is_equal instead of assert_equality_to_constant

        // let prod = prod.reduce(&mut cs.namespace(|| "x*inv mod P"))?;
        // prod.assert_equality_to_constant(&mut cs.namespace(|| "x*inv = 1"), &Self::one())?;

        Self::assert_is_equal(&mut cs.namespace(|| "x*inv = 1 mod P"), &prod, &Self::one())?;

        Ok(inv_alloc)
    }

    pub fn div_unchecked<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // returns self/value (or x/y)

        let x = BlsFp12::from(self);

        let y = BlsFp12::from(value);
        if y.is_zero().into() {
            eprintln!("Inverse of zero element cannot be calculated");
            return Err(SynthesisError::DivisionByZero);
        }
        let y_inv = y.invert().unwrap();
        let div = y_inv * x;

        let div_alloc = Self::alloc_element(&mut cs.namespace(|| "alloc div"), &div)?;

        // y*div = x
        let prod = div_alloc.mul(&mut cs.namespace(|| "y*div"), value)?;
        Self::assert_is_equal(&mut cs.namespace(|| "y*div = x"), &prod, self)?;

        Ok(div_alloc)
    }

    pub fn conditionally_select<CS>(
        cs: &mut CS,
        z0: &Self,
        z1: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = AllocatedE6Element::<F>::conditionally_select(
            &mut cs.namespace(|| "cond b0"),
            &z0.c0,
            &z1.c0,
            condition,
        )?;
        let c1 = AllocatedE6Element::<F>::conditionally_select(
            &mut cs.namespace(|| "cond b1"),
            &z0.c1,
            &z1.c1,
            condition,
        )?;
        Ok(Self { c0, c1 })
    }
}

/// From gnark's std/algebra/emulated/fields_bls12381/e12_pairing.go:
///
///  Torus-based arithmetic:
///
/// After the easy part of the final exponentiation the elements are in a proper
/// subgroup of Fpk (E12) that coincides with some algebraic tori. The elements
/// are in the torus Tk(Fp) and thus in each torus Tk/d(Fp^d) for d|k, d≠k.  We
/// take d=6. So the elements are in T2(Fp6).
/// Let G_{q,2} = {m ∈ Fq^2 | m^(q+1) = 1} where q = p^6.
/// When m.C1 = 0, then m.C0 must be 1 or −1.
///
/// We recall the tower construction:
///
///	𝔽p²[u] = 𝔽p/u²+1
///	𝔽p⁶[v] = 𝔽p²/v³-1-u
///	𝔽p¹²[w] = 𝔽p⁶/w²-v
impl<F: PrimeField + PrimeFieldBits> Torus<F> {
    /// compress_torus compresses x ∈ E12 to (x.C0 + 1)/x.C1 ∈ E6
    pub fn compress_torus<CS>(
        cs: &mut CS,
        x: &AllocatedE12Element<F>,
    ) -> Result<Torus<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // self ∈ G_{q,2} \ {-1,1}
        let y = x.c0.add(
            &mut cs.namespace(|| "y <- x.c0 + 1"),
            &AllocatedE6Element::one(),
        )?;
        let y = y.div_unchecked(&mut cs.namespace(|| "y <- y / x.c1"), &x.c1)?;
        Ok(Torus(y))
    }

    /// decompress_torus decompresses y ∈ E6 to (y+w)/(y-w) ∈ E12
    pub fn decompress_torus<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedE12Element<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let one = AllocatedE6Element::one();
        let n = AllocatedE12Element {
            c0: self.0.clone(),
            c1: one.clone(),
        };
        let d = AllocatedE12Element {
            c0: self.0.clone(),
            c1: one.neg(&mut cs.namespace(|| "-one"))?,
        };

        let x = n.div_unchecked(&mut cs.namespace(|| "x <- n / d"), &d)?;

        Ok(x)
    }

    /// mul_torus multiplies two compressed elements y1, y2 ∈ E6
    /// and returns (y1 * y2 + v)/(y1 + y2)
    /// N.B.: we use mul_torus in the final exponentiation throughout y1 ≠ -y2 always.
    pub fn mul<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (y1, y2) = (&self.0, &value.0);
        let mut n = y1.mul(&mut cs.namespace(|| "n <- y1 * y2"), &y2)?;
        n.b1 = n.b1.add(
            &mut cs.namespace(|| "n.b1 <- n.b1 + 1"),
            &AllocatedE2Element::one(),
        )?;
        let d = y1.add(&mut cs.namespace(|| "d <- y1 + y2"), &y2)?;
        let y3 = n.div_unchecked(&mut cs.namespace(|| "y3 <- n / d"), &d)?;

        Ok(Torus(y3))
    }

    /// inverse_torus inverses a compressed elements y ∈ E6
    /// and returns -y
    pub fn inverse<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Ok(Torus(self.0.neg(&mut cs.namespace(|| "inverse_torus"))?))
    }

    /// square_torus squares a compressed elements y ∈ E6
    /// and returns (y + v/y)/2
    ///
    /// It uses a hint to verify that (2x-y)y = v saving one E6 AssertIsEqual.
    pub fn square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    /// frobenius_torus raises a compressed elements y ∈ E6 to the modulus p
    /// and returns y^p / v^((p-1)/2)
    pub fn frobenius<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    /// frobenius_square_torus raises a compressed elements y ∈ E6 to the square modulus p^2
    /// and returns y^(p^2) / v^((p^2-1)/2)
    pub fn frobenius_square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }
}
