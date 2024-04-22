use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::fp12::Fp12 as BlsFp12;
use bls12_381::fp6::Fp6 as BlsFp6;
use ff::PrimeFieldBits;

use super::fp::FpElement;
use super::fp12::Fp12Element;
use super::fp2::Fp2Element;
use super::fp6::Fp6Element;

#[derive(Clone)]
pub struct Torus<F: PrimeFieldBits>(pub Fp6Element<F>);

/// From gnark's std/algebra/emulated/fields_bls12381/e12_pairing.go:
///
///  Torus-based arithmetic:
///
/// After the easy part of the final exponentiation the elements are in a proper
/// subgroup of Fpk (Fp12) that coincides with some algebraic tori. The elements
/// are in the torus Tk(Fp) and thus in each torus Tk/d(Fp^d) for d|k, d≠k.  We
/// take d=6. So the elements are in T2(Fp6).
/// Let G_{q,2} = {m ∈ Fq^2 | m^(q+1) = 1} where q = p^6.
/// When m.C1 = 0, then m.C0 must be 1 or −1.
///
/// We recall the tower construction:
///
///    𝔽p²[u] = 𝔽p/u²+1
///    𝔽p⁶[v] = 𝔽p²/v³-1-u
///    𝔽p¹²[w] = 𝔽p⁶/w²-v
impl<F: PrimeFieldBits> Torus<F> {
    /// compress_torus compresses x ∈ Fp12 to (x.C0 + 1)/x.C1 ∈ Fp6
    pub fn compress<CS>(cs: &mut CS, x: &Fp12Element<F>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // self ∈ G_{q,2} \ {-1,1}
        let y =
            x.c0.add(&mut cs.namespace(|| "y <- x.c0 + 1"), &Fp6Element::one())?;
        let y = y.div_unchecked(&mut cs.namespace(|| "y <- y div x.c1"), &x.c1)?;
        Ok(Self(y))
    }

    fn compress_native(x: &BlsFp12) -> Result<BlsFp6, SynthesisError> {
        let y = x.c0 + BlsFp6::one();

        if x.c1.is_zero().into() {
            eprintln!("Inverse of zero element cannot be calculated");
            return Err(SynthesisError::DivisionByZero);
        }
        let div = x.c1.invert().unwrap();

        let y = y * div;
        Ok(y)
    }

    /// decompress_torus decompresses y ∈ Fp6 to (y+w)/(y-w) ∈ Fp12
    pub fn decompress<CS>(&self, cs: &mut CS) -> Result<Fp12Element<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let one = Fp6Element::one();
        let neg_one = one.neg(&mut cs.namespace(|| "-1"))?;
        let n = Fp12Element {
            c0: self.0.clone(),
            c1: one,
        };
        let d = Fp12Element {
            c0: self.0.clone(),
            c1: neg_one,
        };

        let x = n.div_unchecked(&mut cs.namespace(|| "x <- n div d"), &d)?;

        Ok(x)
    }

    fn decompress_native(val: &BlsFp6) -> Result<BlsFp12, SynthesisError> {
        let n = BlsFp12 {
            c0: *val,
            c1: BlsFp6::one(),
        };
        let d = BlsFp12 {
            c0: *val,
            c1: -BlsFp6::one(),
        };
        if d.is_zero().into() {
            eprintln!("Inverse of zero element cannot be calculated");
            return Err(SynthesisError::DivisionByZero);
        }
        let div = d.invert().unwrap();

        let x = n * div;
        Ok(x)
    }

    /// mul_torus multiplies two compressed elements y1, y2 ∈ Fp6
    /// and returns (y1 * y2 + v)/(y1 + y2)
    /// N.B.: we use mul_torus in the final exponentiation throughout y1 ≠ -y2 always.
    pub fn mul<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let (y1, y2) = (&self.0, &value.0);
        let mut n = y1.mul(&mut cs.namespace(|| "n <- y1 * y2"), y2)?;
        n.b1 =
            n.b1.add(&mut cs.namespace(|| "n.b1 <- n.b1 + 1"), &Fp2Element::one())?;
        let d = y1.add(&mut cs.namespace(|| "d <- y1 + y2"), y2)?;
        let y3 = n.div_unchecked(&mut cs.namespace(|| "y3 <- n div d"), &d)?;

        Ok(Self(y3))
    }

    /// inverse_torus inverses a compressed elements y ∈ Fp6
    /// and returns -y
    pub fn inverse<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Ok(Self(self.0.neg(&mut cs.namespace(|| "inverse_torus"))?))
    }

    /// square_torus squares a compressed elements y ∈ Fp6
    /// and returns (y + v/y)/2
    ///
    /// It uses a hint to verify that (2x-y)y = v saving one Fp6 AssertIsEqual.
    pub fn square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let y = &self.0;

        let val = BlsFp6::try_from(y).ok().and_then(|val| {
            Self::decompress_native(&val)
                .ok()
                .map(|val| val.square()) // NOTE: could be cyclotomic_square, but I think that only makes it faster? Which doesn't matter in the evaluation
                .and_then(|val| Self::compress_native(&val).ok())
        });

        let sq_alloc =
            Fp6Element::<F>::alloc_element(&mut cs.namespace(|| "alloc torus square"), &val)?; // x

        // v = (2x-y)y
        let v = sq_alloc.double(&mut cs.namespace(|| "v <- v.double()"))?;
        let v = v.sub(&mut cs.namespace(|| "v <- v - y"), y)?;
        let v = v.mul(&mut cs.namespace(|| "v <- v * y"), y)?;

        let expected = Fp6Element {
            b0: Fp2Element::zero(),
            b1: Fp2Element::one(),
            b2: Fp2Element::zero(),
        };
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "v = Fp6(0, 1, 0)"), &v, &expected)?;

        Ok(Self(sq_alloc))
    }

    /// frobenius_torus raises a compressed elements y ∈ Fp6 to the modulus p
    /// and returns y^p / v^((p-1)/2)
    pub fn frobenius<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let y = &self.0;
        let mut cs = cs.namespace(|| "Torus::frobenius(y)");
        let t0 =
            y.b0.conjugate(&mut cs.namespace(|| "t0 <- y.b0.conjugate()"))?;
        let t1 =
            y.b1.conjugate(&mut cs.namespace(|| "t1 <- y.b1.conjugate()"))?;
        let t2 =
            y.b2.conjugate(&mut cs.namespace(|| "t2 <- y.b1.conjugate()"))?;
        let t1 =
            t1.mul_by_nonresidue_1pow2(&mut cs.namespace(|| "t1 <- t1.mul_by_nonresidue_1pow2()"))?;
        let t2 =
            t2.mul_by_nonresidue_1pow4(&mut cs.namespace(|| "t2 <- t2.mul_by_nonresidue_1pow4()"))?;

        let v0 = Fp2Element::<F>::from_dec("877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230", "877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230").unwrap();
        let res = Fp6Element {
            b0: t0,
            b1: t1,
            b2: t2,
        };
        let res = res.mul_by_0(&mut cs.namespace(|| "res <- res.mul_by_0(v0)"), &v0)?;

        Ok(Self(res))
    }

    /// frobenius_square_torus raises a compressed elements y ∈ Fp6 to the square modulus p^2
    /// and returns y^(p^2) / v^((p^2-1)/2)
    pub fn frobenius_square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let y = &self.0;
        let mut cs = cs.namespace(|| "Torus::frobenius_square(y)");
        let v0 = FpElement::<F>::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437").unwrap();
        let t0 =
            y.b0.mul_element(&mut cs.namespace(|| "t0 <- y.b0 * elm(v0)"), &v0)?;
        let t1 = y
            .b1
            .mul_by_nonresidue_2pow2(&mut cs.namespace(|| "t1 <- y.b1.mul_by_nonresidue_2pow2"))?;
        let t1 = t1.mul_element(&mut cs.namespace(|| "t1 <- t1 * elm(v0)"), &v0)?;
        let t2 = y
            .b2
            .mul_by_nonresidue_2pow4(&mut cs.namespace(|| "t2 <- y.b2.mul_by_nonresidue_2pow2"))?;
        let t2 = t2.mul_element(&mut cs.namespace(|| "t2 <- t2 * elm(v0)"), &v0)?;

        Ok(Self(Fp6Element {
            b0: t0,
            b1: t1,
            b2: t2,
        }))
    }

    pub fn n_square<CS>(&self, cs: &mut CS, n: usize) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut x = Some(self);
        let mut tmp = None;
        let mut cs = cs.namespace(|| format!("Torus::n_square(x, {n})"));
        for i in 0..n {
            if let Some(x_val) = x {
                tmp = Some(x_val.square(&mut cs.namespace(|| format!("x <- x.square() ({i})")))?);
                x = tmp.as_ref();
            }
        }

        Ok(tmp.unwrap())
    }

    /// expt_half_torus set z to x^(t/2) in Fp6 and return z
    /// const t/2 uint64 = 7566188111470821376 // negative
    pub fn expt_half<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self;
        let mut cs = cs.namespace(|| "Torus::expt_half(x)");

        // FixedExp computation is derived from the addition chain:
        //
        //  _10      = 2*1
        //  _11      = 1 + _10
        //  _1100    = _11 << 2
        //  _1101    = 1 + _1100
        //  _1101000 = _1101 << 3
        //  _1101001 = 1 + _1101000
        //  return     ((_1101001 << 9 + 1) << 32 + 1) << 15
        //
        // Operations: 62 squares 5 multiplies
        //
        // Generated by github.com/mmcloughlin/addchain v0.4.0.

        let z = x.square(&mut cs.namespace(|| "Step 1: z = x^0x2"))?;

        let z = x.mul(&mut cs.namespace(|| "Step 2: z = x^0x3"), &z)?;

        let z = z.square(&mut cs.namespace(|| "Step 3: z = x^0x6"))?;

        let z = z.square(&mut cs.namespace(|| "Step 4: z = x^0xc"))?;

        let z = x.mul(&mut cs.namespace(|| "Step 5: z = x^0xd"), &z)?;

        let z = z.n_square(&mut cs.namespace(|| "Step 8: z = x^0x68"), 3)?;

        let z = x.mul(&mut cs.namespace(|| "Step 9: z = x^0x69"), &z)?;

        let z = z.n_square(&mut cs.namespace(|| "Step 18: z = x^0xd200"), 9)?;

        let z = x.mul(&mut cs.namespace(|| "Step 19: z = x^0xd201"), &z)?;

        let z = z.n_square(&mut cs.namespace(|| "Step 51: z = x^0xd20100000000"), 32)?;

        let z = x.mul(&mut cs.namespace(|| "Step 52: z = x^0xd20100000001"), &z)?;

        let z = z.n_square(
            &mut cs.namespace(|| "Step 67: z = x^0x6900800000008000"),
            15,
        )?;

        let z = z.inverse(&mut cs.namespace(|| "Final step: z = z.inverse()"))?;

        Ok(z)
    }

    /// expt set z to xᵗ in Fp6 and return z
    /// const t uint64 = 15132376222941642752 // negative
    pub fn expt<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self;
        let mut cs = cs.namespace(|| "Torus::expt(x)");
        let z = x.expt_half(&mut cs.namespace(|| "z <- x.expt_half()"))?;
        let z = z.square(&mut cs.namespace(|| "z <- z.square()"))?;
        Ok(z)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use halo2curves::bn256::Fq as Fp;

    use expect_test::{expect, Expect};
    fn expect_eq(computed: usize, expected: &Expect) {
        expected.assert_eq(&computed.to_string());
    }

    #[test]
    fn test_random_compress() {
        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let c = Torus::<Fp>::compress_native(&a).unwrap();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res_alloc = Torus::compress(&mut cs.namespace(|| "a.torus()"), &a_alloc).unwrap();
        Fp6Element::assert_is_equal(
            &mut cs.namespace(|| "a.torus() = c"),
            &res_alloc.0,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["6541"]);
        expect_eq(cs.num_constraints(), &expect!["6433"]);
    }

    #[test]
    fn test_random_decompress() {
        let mut rng = rand::thread_rng();
        let a = BlsFp6::random(&mut rng);
        let c = Torus::<Fp>::decompress_native(&a).unwrap();

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let c_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let res = Torus(a_alloc);
        let res_alloc = res
            .decompress(&mut cs.namespace(|| "a.decompress()"))
            .unwrap();
        Fp12Element::assert_is_equal(
            &mut cs.namespace(|| "a.decompress() = c"),
            &res_alloc,
            &c_alloc,
        )
        .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["13116"]);
        expect_eq(cs.num_constraints(), &expect!["13026"]);
    }

    #[test]
    fn test_random_mul() {
        use bls12_381::fp2::Fp2 as BlsFp2;
        use std::ops::{Add, Mul};

        let mut rng = rand::thread_rng();
        let a = BlsFp12::random(&mut rng);
        let b = BlsFp12::random(&mut rng);
        let ta = Torus::<Fp>::compress_native(&a).unwrap();
        let tb = Torus::<Fp>::compress_native(&b).unwrap();
        // it seems that torus multiplication is its own operation, so we would need to replicate the logic natively here
        let c = {
            let (y1, y2) = (ta, tb);
            let mut n = y1.mul(y2);
            n.c1 += BlsFp2::one();
            let d = y1.add(y2);
            n * d.invert().unwrap()
        };

        let mut cs = TestConstraintSystem::<Fp>::new();
        let a_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc a"), &Some(a)).unwrap();
        let b_alloc =
            Fp12Element::alloc_element(&mut cs.namespace(|| "alloc b"), &Some(b)).unwrap();
        let c_alloc = Fp6Element::alloc_element(&mut cs.namespace(|| "alloc c"), &Some(c)).unwrap();
        let a_alloc = Torus::compress(&mut cs.namespace(|| "a <- a.torus()"), &a_alloc).unwrap();
        let b_alloc = Torus::compress(&mut cs.namespace(|| "b <- b.torus()"), &b_alloc).unwrap();
        let res_alloc = a_alloc.mul(&mut cs.namespace(|| "a*b"), &b_alloc).unwrap();
        Fp6Element::assert_is_equal(&mut cs.namespace(|| "a*b = c"), &res_alloc.0, &c_alloc)
            .unwrap();
        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        expect_eq(cs.num_inputs(), &expect!["1"]);
        expect_eq(cs.scalar_aux().len(), &expect!["16981"]);
        expect_eq(cs.num_constraints(), &expect!["16777"]);
    }
}
