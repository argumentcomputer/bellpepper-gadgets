use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_emulated::field_element::{
    EmulatedFieldElement, EmulatedFieldParams, PseudoMersennePrime,
};
use ff::PrimeFieldBits;
use num_bigint::BigInt;

use crate::{
    curve::{AffinePoint, Ed25519Curve},
    field::Fe25519,
};

const DEFAULT_SCALAR_MULT_WINDOW_SIZE: i32 = 4;

struct Ed25519FpParams;

impl EmulatedFieldParams for Ed25519FpParams {
    fn num_limbs() -> usize {
        5
    }

    fn bits_per_limb() -> usize {
        51
    }

    fn modulus() -> BigInt {
        BigInt::parse_bytes(
            b"7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed",
            16,
        )
        .unwrap()
    }

    fn is_modulus_pseudo_mersenne() -> bool {
        true
    }

    fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
        Some(PseudoMersennePrime {
            e: 255,
            c: BigInt::from(19),
        })
    }
}

type Ed25519Fp<F> = EmulatedFieldElement<F, Ed25519FpParams>;

impl<F> From<&Fe25519> for Ed25519Fp<F>
where
    F: PrimeFieldBits,
{
    fn from(value: &Fe25519) -> Self {
        Self::from(&value.0)
    }
}

#[derive(Clone)]
pub struct AllocatedAffinePoint<F: PrimeFieldBits> {
    x: Ed25519Fp<F>,
    y: Ed25519Fp<F>,
    value: AffinePoint,
}

impl<F: PrimeFieldBits> AllocatedAffinePoint<F> {
    pub fn get_point(&self) -> AffinePoint {
        self.value.clone()
    }

    pub fn alloc_affine_point<CS>(cs: &mut CS, value: &AffinePoint) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x_limb_values = Ed25519Fp::<F>::from(&value.x);
        let y_limb_values = Ed25519Fp::<F>::from(&value.y);

        let x =
            x_limb_values.allocate_field_element_unchecked(&mut cs.namespace(|| "allocate x"))?;
        let y =
            y_limb_values.allocate_field_element_unchecked(&mut cs.namespace(|| "allocate y"))?;

        Ok(Self {
            x,
            y,
            value: value.clone(),
        })
    }

    pub fn alloc_identity_point<CS>(cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let identity_value = AffinePoint::default();
        let identity = Self::alloc_affine_point(
            &mut cs.namespace(|| "alloc identity point"),
            &identity_value,
        )?;

        identity.x.assert_equality_to_constant(
            &mut cs.namespace(|| "check x equals 0"),
            &Ed25519Fp::zero(),
        )?;
        identity.y.assert_equality_to_constant(
            &mut cs.namespace(|| "check y equals 1"),
            &Ed25519Fp::one(),
        )?;
        Ok(identity)
    }

    pub fn assert_equality<CS>(cs: &mut CS, p: &Self, q: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x1 = &p.x;
        let y1 = &p.y;

        let x2 = &q.x;
        let y2 = &q.y;

        Ed25519Fp::<F>::assert_is_equal(&mut cs.namespace(|| "x1 == x2"), x1, x2)?;

        Ed25519Fp::<F>::assert_is_equal(&mut cs.namespace(|| "y1 == y2"), y1, y2)?;

        Ok(())
    }

    fn verify_point_addition<CS>(
        cs: &mut CS,
        p: &Self,
        q: &Self,
        r: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x1 = &p.x;
        let y1 = &p.y;
        let x2 = &q.x;
        let y2 = &q.y;
        let x3 = &r.x;
        let y3 = &r.y;

        let one = Ed25519Fp::<F>::from(&Fe25519::one());
        let d = Ed25519Fp::<F>::from(&Ed25519Curve::d());

        let x1x2 = x1.mul(&mut cs.namespace(|| "x1*x2"), x2)?;
        let y1y2 = y1.mul(&mut cs.namespace(|| "y1*y2"), y2)?;
        let x1y2 = x1.mul(&mut cs.namespace(|| "x1*y2"), y2)?;
        let x2y1 = x2.mul(&mut cs.namespace(|| "x2*y1"), y1)?;

        let x1x2y1y2 = x1x2.mul(&mut cs.namespace(|| "x1*x2*y1*y2"), &y1y2)?;
        let dx1x2y1y2 = d.mul(&mut cs.namespace(|| "d*x1*x2*y1*y2"), &x1x2y1y2)?;

        let dx1x2y1y2_plus_1 = one.add(&mut cs.namespace(|| "1 + d*x1*x2*y1*y2"), &dx1x2y1y2)?;
        let neg_dx1x2y1y2_plus_1 =
            one.sub(&mut cs.namespace(|| "1 - d*x1*x2*y1*y2"), &dx1x2y1y2)?;

        let x3_times_denominator = x3.mul(
            &mut cs.namespace(|| "x3*(1 + d*x1*x2*y1*y2)"),
            &dx1x2y1y2_plus_1,
        )?;

        let x1y2_plus_x2y1 = x1y2.add(&mut cs.namespace(|| "x1*y2 + x1*y2"), &x2y1)?;
        Ed25519Fp::<F>::assert_is_equal(
            &mut cs.namespace(|| "x3*(1 + d*x1*x2*y1*y2) == x1*y2 + x2*y1"),
            &x1y2_plus_x2y1,
            &x3_times_denominator,
        )?;

        let y3_times_denominator = y3.mul(
            &mut cs.namespace(|| "y3*(1 - d*x1*x2*y1*y2)"),
            &neg_dx1x2y1y2_plus_1,
        )?;

        let x1x2_plus_y1y2 = x1x2.add(&mut cs.namespace(|| "Reduce x1*x2 + y1*y2"), &y1y2)?;
        Ed25519Fp::<F>::assert_is_equal(
            &mut cs.namespace(|| "y3*(1 - d*x1*x2*y1*y2) == x1*x2 + y1*y2"),
            &y3_times_denominator,
            &x1x2_plus_y1y2,
        )?;

        Ok(())
    }

    pub fn ed25519_point_addition<CS>(
        cs: &mut CS,
        p: &Self,
        q: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let sum_value = &p.value + &q.value;
        let sum = Self::alloc_affine_point(&mut cs.namespace(|| "allocate sum"), &sum_value)?;

        sum.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of sum is in base field"),
        )?;
        sum.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of sum is in base field"),
        )?;

        Self::verify_point_addition(&mut cs.namespace(|| "verify point addition"), p, q, &sum)?;

        Ok(sum)
    }

    fn verify_point_doubling<CS>(
        cs: &mut CS,
        p: &Self,
        doubled_p: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if !p.value.is_on_curve() {
            eprintln!("Input to this method must be a curve point");
            return Err(SynthesisError::Unsatisfiable);
        }

        let x = &p.x;
        let y = &p.y;

        let x2 = x.mul(&mut cs.namespace(|| "x*x"), x)?;
        let y2 = y.mul(&mut cs.namespace(|| "y*y"), y)?;
        let xy = x.mul(&mut cs.namespace(|| "x*y"), y)?;

        // Numerator of doubled_p x-coordinate
        let expected_x_numerator = xy.mul_const(&mut cs.namespace(|| "2*x*y"), &BigInt::from(2))?;
        let minus_x2 = x2.neg(&mut cs.namespace(|| "-x*x"))?;
        // Since curve equation is -x^2 + y^2 = 1 + dx^2y^2, we can calculate the RHS using the LHS
        let doubled_p_x_denominator =
            minus_x2.add(&mut cs.namespace(|| "-x*x+ y*y  a.k.a  1 + d*x*x*y*y"), &y2)?;
        let doubled_p_x_numerator = doubled_p.x.mul(
            &mut cs.namespace(|| "2P.x times (1+d*x*x*y*y)"),
            &doubled_p_x_denominator,
        )?;
        Ed25519Fp::<F>::assert_is_equal(
            &mut cs.namespace(|| "2P.x times (1+d*x*x*y*y) == 2*x*y"),
            &doubled_p_x_numerator,
            &expected_x_numerator,
        )?;

        // Numerator of doubled_p y-coordinate
        let expected_y_numerator = x2.add(&mut cs.namespace(|| "x*x + y*y"), &y2)?;
        let two = Ed25519Fp::<F>::from(&Fe25519::from(2u64));
        let doubled_p_y_denominator = two.sub(
            &mut cs.namespace(|| " 2 - (1 + d*x*x*y*y) = 1 - d*x*x*y*y"),
            &doubled_p_x_denominator,
        )?;
        let doubled_p_y_numerator = doubled_p.y.mul(
            &mut cs.namespace(|| "2P.y times (1-d*x*x*y*y)"),
            &doubled_p_y_denominator,
        )?;
        Ed25519Fp::<F>::assert_is_equal(
            &mut cs.namespace(|| "2P.y times (1-d*x*x*y*y) == x*x + y*y"),
            &doubled_p_y_numerator,
            &expected_y_numerator,
        )?;

        Ok(())
    }

    pub fn ed25519_point_doubling<CS>(cs: &mut CS, p: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let double_value = p.value.double();
        let double_p =
            Self::alloc_affine_point(&mut cs.namespace(|| "allocate 2P"), &double_value)?;

        double_p.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of double point is in base field"),
        )?;
        double_p.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of double point is in base field"),
        )?;

        Self::verify_point_doubling(&mut cs.namespace(|| "verify point doubling"), p, &double_p)?;

        Ok(double_p)
    }

    /// If `condition` is true, return `in1`. Otherwise, return `in0`.
    /// `selector_bits` are little-endian order
    fn conditionally_select<CS>(
        cs: &mut CS,
        inputs: &[Self],
        selector_bits: &[Boolean],
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if inputs.len() != (1usize << selector_bits.len()) {
            eprintln!(
                "Number of inputs {} must be equal to 2^(number of selector bits) = 2^{}",
                inputs.len(),
                selector_bits.len(),
            );
            return Err(SynthesisError::Unsatisfiable);
        }
        let inputs_x = inputs.iter().map(|i| i.x.clone()).collect::<Vec<_>>();
        let inputs_y = inputs.iter().map(|i| i.y.clone()).collect::<Vec<_>>();

        let x = EmulatedFieldElement::mux_tree(
            &mut cs.namespace(|| "allocate value of output x coordinate"),
            selector_bits.iter().rev(), // mux_tree requires MSB first
            &inputs_x,
        )?;
        let y = EmulatedFieldElement::mux_tree(
            &mut cs.namespace(|| "allocate value of output y coordinate"),
            selector_bits.iter().rev(), // mux_tree requires MSB first
            &inputs_y,
        )?;

        let mut res_index = 0usize;
        for (i, b) in selector_bits.iter().enumerate() {
            if b.get_value().unwrap() {
                res_index += 1 << i;
            }
        }
        let value = inputs[res_index].value.clone();

        Ok(Self { x, y, value })
    }

    pub fn ed25519_scalar_multiplication_windowed<CS>(
        &self,
        cs: &mut CS,
        scalar: &[Boolean],
        window_size: i32,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if window_size <= 0 {
            eprintln!("Window size must be positive");
            return Err(SynthesisError::Unsatisfiable);
        };
        if scalar.len() < window_size as usize {
            eprintln!("Scalar bit vector cannot be shorter than window size");
            return Err(SynthesisError::Unsatisfiable);
        };
        if scalar.len() >= 254usize {
            // the largest curve25519 scalar fits in 253 bits
            eprintln!("Scalar bit vector has more than 253 bits");
            return Err(SynthesisError::Unsatisfiable);
        }

        // No range checks on limbs required as it is checked to be equal to (0,1)
        let identity_point =
            Self::alloc_identity_point(&mut cs.namespace(|| "allocate identity point"))?;

        // Remember to avoid field membership checks before calling this function
        self.x.check_field_membership(
            &mut cs.namespace(|| "check x coordinate of base point is in base field"),
        )?;
        self.y.check_field_membership(
            &mut cs.namespace(|| "check y coordinate of base point is in base field"),
        )?;

        let mut lookup_table: Vec<Self> = vec![];
        lookup_table.push(identity_point);
        lookup_table.push(self.clone());

        for i in 2..(1usize << window_size) {
            if i % 2 == 0 {
                lookup_table.push(Self::ed25519_point_doubling(
                    &mut cs.namespace(|| format!("allocate {i} times the base")),
                    &lookup_table[i / 2],
                )?);
            } else {
                lookup_table.push(Self::ed25519_point_addition(
                    &mut cs.namespace(|| format!("allocate {i} times the base")),
                    &lookup_table[i - 1],
                    self,
                )?);
            };
        }

        let n: i32 = (scalar.len() - 1) as i32;

        let mut window_bits: Vec<Boolean> = vec![];
        for i in 0..window_size {
            window_bits.push(scalar[(n - window_size + 1 + i) as usize].clone())
        }

        let mut output = Self::conditionally_select(
            &mut cs.namespace(|| "allocate initial value of output"),
            &lookup_table,
            &window_bits,
        )?;

        let mut i: i32 = n - window_size;
        while i >= window_size - 1 {
            for j in 0..window_size {
                output = Self::ed25519_point_doubling(
                    &mut cs.namespace(|| format!("doubling number {} in iteration {i}", j + 1)),
                    &output,
                )?;
            }

            window_bits.clear();
            for j in 0..window_size {
                window_bits.push(scalar[(i - window_size + 1 + j) as usize].clone())
            }

            let tmp = Self::conditionally_select(
                &mut cs.namespace(|| format!("allocate tmp value in iteration {i}")),
                &lookup_table,
                &window_bits,
            )?;

            output = Self::ed25519_point_addition(
                &mut cs.namespace(|| format!("allocate sum of output and tmp in iteration {i}")),
                &output,
                &tmp,
            )?;

            i -= window_size;
        }

        let num_remaining_bits = scalar.len() % (window_size as usize);

        if num_remaining_bits != 0 {
            for j in 0..num_remaining_bits {
                output = Self::ed25519_point_doubling(
                    &mut cs.namespace(|| format!("final output doubling number {}", j + 1)),
                    &output,
                )?;
            }
            let tmp = Self::ed25519_point_addition(
                &mut cs.namespace(|| format!("sum of {}*output and base", 1 << num_remaining_bits)),
                &output,
                self,
            )?;

            let mut final_lookup_table = vec![];
            final_lookup_table.push(output.clone());
            final_lookup_table.push(tmp);

            #[allow(clippy::needless_range_loop)]
            for j in 2..(1usize << num_remaining_bits) {
                let tmp = Self::ed25519_point_addition(
                    &mut cs.namespace(|| {
                        format!("sum of {}*output and {j}*base", 1 << num_remaining_bits)
                    }),
                    &output,
                    &lookup_table[j],
                )?;
                final_lookup_table.push(tmp);
            }

            window_bits.clear();
            window_bits = scalar[..num_remaining_bits].to_vec();

            output = Self::conditionally_select(
                &mut cs.namespace(|| "final doubling of output"),
                &final_lookup_table,
                &window_bits,
            )?;
        }

        Ok(output)
    }

    pub fn ed25519_scalar_multiplication<CS>(
        &self,
        cs: &mut CS,
        scalar: &[Boolean],
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Self::ed25519_scalar_multiplication_windowed(
            self,
            &mut cs.namespace(|| {
                format!("scalar multiplication with window {DEFAULT_SCALAR_MULT_WINDOW_SIZE}")
            }),
            scalar,
            DEFAULT_SCALAR_MULT_WINDOW_SIZE,
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::curve::Ed25519Curve;

    use super::*;
    use bellpepper::util_cs::metric_cs::MetricCS;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use num_bigint::{BigUint, RandBigInt};
    use num_integer::Integer;
    use num_traits::Zero;
    use pasta_curves::Fp;

    fn random_point() -> AffinePoint {
        let mut rng = rand::thread_rng();
        let mut point = AffinePoint::default();
        loop {
            let y = Fe25519::random(&mut rng);
            let y_sq = &y.square();
            let x_sq = (y_sq - &Fe25519::one())
                * (Ed25519Curve::d() * y_sq + Fe25519::one())
                    .invert()
                    .unwrap();

            let x = x_sq.sqrt();
            if let Some(x) = x {
                point.x = x;
                point.y = y;
                break;
            }
        }
        point
    }

    #[test]
    fn alloc_affine_point_equality() {
        for _ in 0..50 {
            let p = random_point();

            let mut cs = TestConstraintSystem::<Fp>::new();

            let p_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc point p"), &p);
            let p_al = p_alloc.unwrap();

            let _ =
                AllocatedAffinePoint::assert_equality(&mut cs.namespace(|| "p == p"), &p_al, &p_al);

            if !cs.is_satisfied() {
                eprintln!("{:?}", cs.which_is_unsatisfied())
            }
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 316);
            assert_eq!(cs.num_inputs(), 1);
        }

        for _ in 0..50 {
            let p = random_point();
            assert!(Ed25519Curve::is_on_curve(&p));
            let q = random_point();
            assert!(Ed25519Curve::is_on_curve(&q));

            let mut cs = TestConstraintSystem::<Fp>::new();

            let p_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc point p"), &p);
            let p_al = p_alloc.unwrap();

            let q_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc point q"), &q);
            let q_al = q_alloc.unwrap();

            let _ =
                AllocatedAffinePoint::assert_equality(&mut cs.namespace(|| "p == q"), &p_al, &q_al);

            if cs.is_satisfied() {
                assert!(
                    Ed25519Curve::check_equality(&p_al.value, &q_al.value),
                    "p and q are equal"
                );
            }

            assert_eq!(cs.num_constraints(), 316);
            assert_eq!(cs.num_inputs(), 1);
        }
    }

    #[test]
    fn alloc_affine_point_addition() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
        let scalar = rng.gen_biguint_range(&BigUint::zero(), &Ed25519Curve::order());
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let scalar = rng.gen_biguint_range(&BigUint::zero(), &Ed25519Curve::order());
        let q = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let sum_expected_value = &p + &q;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let p_alloc =
            AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc point p"), &p);
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        let q_alloc =
            AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc point q"), &q);
        assert!(q_alloc.is_ok());
        let q_al = q_alloc.unwrap();

        let sum_alloc = AllocatedAffinePoint::ed25519_point_addition(
            &mut cs.namespace(|| "adding p and q"),
            &p_al,
            &q_al,
        );
        assert!(sum_alloc.is_ok());
        let sum_al = sum_alloc.unwrap();

        assert_eq!(sum_expected_value, sum_al.value);

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 3941);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn alloc_affine_point_doubling() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
        let scalar = rng.gen_biguint_range(&BigUint::zero(), &Ed25519Curve::order());
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let double_expected_value = p.double();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let p_alloc =
            AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc point p"), &p);
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        let double_alloc =
            AllocatedAffinePoint::ed25519_point_doubling(&mut cs.namespace(|| "doubling p"), &p_al);
        assert!(double_alloc.is_ok());
        let double_al = double_alloc.unwrap();

        assert_eq!(double_expected_value, double_al.value);

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 2003);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn alloc_affine_scalar_multiplication_default() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();

        let mut scalar = rng.gen_biguint(256u64);
        scalar >>= 3; // scalar now has 253 significant bits
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);

        let mut scalar_vec: Vec<Boolean> = vec![];
        for _i in 0..253 {
            if scalar.is_odd() {
                scalar_vec.push(Boolean::constant(true))
            } else {
                scalar_vec.push(Boolean::constant(false))
            };
            scalar >>= 1;
        }

        let mut cs = TestConstraintSystem::<Fp>::new();

        let b_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "allocate base point"),
            &b,
        );
        assert!(b_alloc.is_ok());
        let b_al = b_alloc.unwrap();

        let p_alloc = b_al.ed25519_scalar_multiplication(
            &mut cs.namespace(|| "scalar multiplication"),
            &scalar_vec,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        assert_eq!(p, p_al.value);

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 798_750);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn alloc_affine_scalar_multiplication_window_range() {
        assert_eq!(scalar_multiplication_helper(1), 1_501_070);
        assert_eq!(scalar_multiplication_helper(2), 1_009_705);
        assert_eq!(scalar_multiplication_helper(3), 856_168);
        assert_eq!(scalar_multiplication_helper(4), 798_750);
        assert_eq!(scalar_multiplication_helper(5), 822_822);
    }

    fn scalar_multiplication_helper(window_size: i32) -> usize {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();

        let mut scalar = rng.gen_biguint(256u64);
        scalar >>= 3; // scalar now has 253 significant bits
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);

        let mut scalar_vec: Vec<Boolean> = vec![];
        for _i in 0..253 {
            if scalar.is_odd() {
                scalar_vec.push(Boolean::constant(true))
            } else {
                scalar_vec.push(Boolean::constant(false))
            };
            scalar >>= 1;
        }

        let mut cs = TestConstraintSystem::<Fp>::new();

        let b_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "allocate base point"),
            &b,
        );
        assert!(b_alloc.is_ok());
        let b_al = b_alloc.unwrap();

        let p_alloc = b_al.ed25519_scalar_multiplication_windowed(
            &mut cs.namespace(|| "scalar multiplication"),
            &scalar_vec,
            window_size,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        assert_eq!(p, p_al.value);

        assert!(cs.is_satisfied());
        cs.num_constraints()
    }

    #[test]
    fn alloc_affine_scalar_multiplication_metric_cs() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();

        let mut scalar = rng.gen_biguint(256u64);
        scalar >>= 3; // scalar now has 253 significant bits
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);

        let mut scalar_vec: Vec<Boolean> = vec![];
        for _i in 0..253 {
            if scalar.is_odd() {
                scalar_vec.push(Boolean::constant(true))
            } else {
                scalar_vec.push(Boolean::constant(false))
            };
            scalar >>= 1;
        }

        let mut cs = MetricCS::<Fp>::new();

        let b_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "allocate base point"),
            &b,
        );
        assert!(b_alloc.is_ok());
        let b_al = b_alloc.unwrap();

        let p_alloc = b_al.ed25519_scalar_multiplication(
            &mut cs.namespace(|| "scalar multiplication"),
            &scalar_vec,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        assert_eq!(p, p_al.value);

        assert_eq!(cs.num_constraints(), 798_750);
        assert_eq!(cs.num_inputs(), 1);
    }
}
