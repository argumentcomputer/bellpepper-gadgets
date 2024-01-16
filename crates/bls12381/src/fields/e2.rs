use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bls12_381::fp::Fp as BlsFp;
use bls12_381::fp2::Fp2 as BlsFp2;
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigInt;

use super::fp::{bigint_to_fpelem, AllocatedFieldElement};

#[derive(Clone)]
pub struct AllocatedE2Element<F: PrimeField + PrimeFieldBits> {
    pub(crate) a0: AllocatedFieldElement<F>,
    pub(crate) a1: AllocatedFieldElement<F>,
}

impl<F> From<&BlsFp2> for AllocatedE2Element<F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &BlsFp2) -> Self {
        let a0 = AllocatedFieldElement::<F>::from(&value.c0);
        let a1 = AllocatedFieldElement::<F>::from(&value.c1);
        Self { a0, a1 }
    }
}

impl<F> From<&AllocatedE2Element<F>> for BlsFp2
where
    F: PrimeField + PrimeFieldBits,
{
    fn from(value: &AllocatedE2Element<F>) -> Self {
        let c0 = BlsFp::from(&value.a0);
        let c1 = BlsFp::from(&value.a1);
        BlsFp2 { c0, c1 }
    }
}

pub fn bigint_to_e2elem(val: (&BigInt, &BigInt)) -> Option<BlsFp2> {
    let c0 = bigint_to_fpelem(val.0).unwrap();
    let c1 = bigint_to_fpelem(val.1).unwrap();
    Some(BlsFp2 { c0, c1 })
}

impl<F: PrimeField + PrimeFieldBits> AllocatedE2Element<F> {
    pub fn from_dec(val: (&str, &str)) -> Result<Self, SynthesisError> {
        let c0 = AllocatedFieldElement::from_dec(val.0)?;
        let c1 = AllocatedFieldElement::from_dec(val.1)?;
        Ok(Self { a0: c0, a1: c1 })
    }

    pub fn zero() -> Self {
        Self {
            a0: AllocatedFieldElement::zero(),
            a1: AllocatedFieldElement::zero(),
        }
    }

    pub fn one() -> Self {
        Self {
            a0: AllocatedFieldElement::one(),
            a1: AllocatedFieldElement::zero(),
        }
    }

    pub fn non_residue() -> Self {
        Self {
            a0: AllocatedFieldElement::one(),
            a1: AllocatedFieldElement::one(),
        }
    }

    pub fn alloc_element<CS>(cs: &mut CS, value: &BlsFp2) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a0 = AllocatedFieldElement::<F>::alloc_element(
            &mut cs.namespace(|| "allocate a0"),
            &value.c0,
        )?;
        let a1 = AllocatedFieldElement::<F>::alloc_element(
            &mut cs.namespace(|| "allocate a1"),
            &value.c1,
        )?;

        Ok(Self { a0, a1 })
    }

    pub fn assert_is_equal<CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        AllocatedFieldElement::<F>::assert_is_equal(
            &mut cs.namespace(|| "a0 =? a0"),
            &a.a0,
            &b.a0,
        )?;
        AllocatedFieldElement::<F>::assert_is_equal(
            &mut cs.namespace(|| "a1 =? a1"),
            &a.a1,
            &b.a1,
        )?;
        Ok(())
    }

    pub fn reduce<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a0_reduced = self.a0.reduce(&mut cs.namespace(|| "a0 mod P"))?;
        let a1_reduced = self.a1.reduce(&mut cs.namespace(|| "a1 mod P"))?;
        Ok(Self {
            a0: a0_reduced,
            a1: a1_reduced,
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
        self.a0
            .assert_equality_to_constant(&mut cs.namespace(|| "a0 =? (const) a0"), &constant.a0)?;
        self.a1
            .assert_equality_to_constant(&mut cs.namespace(|| "a1 =? (const) a1"), &constant.a1)?;
        Ok(())
    }

    pub fn alloc_is_zero<CS>(&self, cs: &mut CS) -> Result<AllocatedBit, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let z0 = self.a0.alloc_is_zero(&mut cs.namespace(|| "a0 =? 0"))?;
        let z1 = self.a1.alloc_is_zero(&mut cs.namespace(|| "a1 =? 0"))?;
        AllocatedBit::and(&mut cs.namespace(|| "and(z0, z1)"), &z0, &z1)
    }

    pub fn add<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a0 = self
            .a0
            .add(&mut cs.namespace(|| "compute a0 + a0"), &value.a0)?;
        let a1 = self
            .a1
            .add(&mut cs.namespace(|| "compute a1 + a1"), &value.a1)?;
        Ok(Self { a0, a1 })
    }

    pub fn sub<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a0 = self
            .a0
            .sub(&mut cs.namespace(|| "compute a0 - a0"), &value.a0)?;
        let a1 = self
            .a1
            .sub(&mut cs.namespace(|| "compute a1 - a1"), &value.a1)?;
        Ok(Self { a0, a1 })
    }

    pub fn mul<CS>(&self, cs: &mut CS, value: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut cs = cs.namespace(|| "compute e2 mul(x,y)");
        let a = self
            .a0
            .add(&mut cs.namespace(|| "a <- x.a0 + x.a1"), &self.a1)?;
        let b = value
            .a0
            .add(&mut cs.namespace(|| "b <- y.a0 + y.a1"), &value.a1)?;

        let a = a.mul(&mut cs.namespace(|| "a <- a * b"), &b)?;

        let b = self
            .a0
            .mul(&mut cs.namespace(|| "b <- x.a0 * y.a0"), &value.a0)?;

        let c = self
            .a1
            .mul(&mut cs.namespace(|| "c <- x.a1 * y.a1"), &value.a1)?;

        let z1 = a.sub(&mut cs.namespace(|| "z1 <- a - b"), &b)?;
        let z1 = z1.sub(&mut cs.namespace(|| "z1 <- z1 - c"), &c)?;

        let z0 = b.sub(&mut cs.namespace(|| "z0 <- b - c"), &c)?;

        Ok(Self { a0: z0, a1: z1 })
    }

    /// mul_by_nonresidue returns returns x*(1+u)
    pub fn mul_by_nonresidue<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a = self
            .a0
            .sub(&mut cs.namespace(|| "a <- x.a0 - x.a1"), &self.a1)?;
        let b = self
            .a0
            .add(&mut cs.namespace(|| "b <- x.a0 + x.a1"), &self.a1)?;
        Ok(Self { a0: a, a1: b })
    }

    /// mul_by_nonresidue_1pow1 returns x*(1+u)^(1*(p^1-1)/6)
    pub fn mul_by_nonresidue_1pow1<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = Self::from_dec(("3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760", "151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027"))?;
        self.mul(&mut cs.namespace(|| "e2.mul_by_nonresidue_1pow5"), &elm)
    }

    /// mul_by_nonresidue_1pow2 returns x*(1+u)^(2*(p^1-1)/6)
    pub fn mul_by_nonresidue_1pow2<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = AllocatedFieldElement::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436")?;
        let a = self.a1.mul(&mut cs.namespace(|| "a <- x.a1 * elm"), &elm)?;
        let a = a.neg(&mut cs.namespace(|| "a <- a.neg()"))?;
        let b = self.a0.mul(&mut cs.namespace(|| "b <- x.a0 * elm"), &elm)?;
        Ok(Self { a0: a, a1: b })
    }

    /// mul_by_nonresidue_1pow3 returns x*(1+u)^(3*(p^1-1)/6)
    pub fn mul_by_nonresidue_1pow3<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = Self::from_dec(("1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257", "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257"))?;
        self.mul(&mut cs.namespace(|| "e2.mul_by_nonresidue_1pow3"), &elm)
    }

    /// mul_by_nonresidue_1pow4 returns x*(1+u)^(4*(p^1-1)/6)
    pub fn mul_by_nonresidue_1pow4<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = AllocatedFieldElement::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437")?;
        self.mul_element(&mut cs.namespace(|| "e2.mul_by_nonresidue_1pow4"), &elm)
    }

    /// mul_by_nonresidue_1pow5 returns x*(1+u)^(5*(p^1-1)/6)
    pub fn mul_by_nonresidue_1pow5<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = Self::from_dec(("877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230", "3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557"))?;
        self.mul(&mut cs.namespace(|| "e2.mul_by_nonresidue_1pow5"), &elm)
    }

    /// mul_by_nonresidue_2pow1 returns x*(1+u)^(1*(p^2-1)/6)
    pub fn mul_by_nonresidue_2pow1<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = AllocatedFieldElement::from_dec("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351")?;
        self.mul_element(&mut cs.namespace(|| "e2.mul_by_nonresidue_2pow1"), &elm)
    }

    /// mul_by_nonresidue_2pow2 returns x*(1+u)^(2*(p^2-1)/6)
    pub fn mul_by_nonresidue_2pow2<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = AllocatedFieldElement::from_dec("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350")?;
        self.mul_element(&mut cs.namespace(|| "e2.mul_by_nonresidue_2pow2"), &elm)
    }

    /// mul_by_nonresidue_2pow3 returns x*(1+u)^(3*(p^2-1)/6)
    pub fn mul_by_nonresidue_2pow3<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = AllocatedFieldElement::from_dec("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786")?;
        self.mul_element(&mut cs.namespace(|| "e2.mul_by_nonresidue_2pow3"), &elm)
    }

    /// mul_by_nonresidue_2pow4 returns x*(1+u)^(4*(p^2-1)/6)
    pub fn mul_by_nonresidue_2pow4<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = AllocatedFieldElement::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436")?;
        self.mul_element(&mut cs.namespace(|| "e2.mul_by_nonresidue_2pow4"), &elm)
    }

    /// mul_by_nonresidue_2pow5 returns x*(1+u)^(5*(p^2-1)/6)
    pub fn mul_by_nonresidue_2pow5<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elm = AllocatedFieldElement::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437")?;
        self.mul_element(&mut cs.namespace(|| "e2.mul_by_nonresidue_2pow5"), &elm)
    }

    pub fn mul_const<CS>(&self, cs: &mut CS, value: &BigInt) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a0 = self
            .a0
            .mul_const(&mut cs.namespace(|| "a0 * constval"), value)?;
        let a1 = self
            .a1
            .mul_const(&mut cs.namespace(|| "a1 * constval"), value)?;
        Ok(Self { a0, a1 })
    }

    pub fn mul_element<CS>(
        &self,
        cs: &mut CS,
        value: &AllocatedFieldElement<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a0 = self.a0.mul(&mut cs.namespace(|| "a0 * val"), value)?;
        let a1 = self.a1.mul(&mut cs.namespace(|| "a1 * val"), value)?;
        Ok(Self { a0, a1 })
    }

    pub fn neg<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a0 = self.a0.neg(&mut cs.namespace(|| "compute -a0"))?;
        let a1 = self.a1.neg(&mut cs.namespace(|| "compute -a1"))?;
        Ok(Self { a0, a1 })
    }

    pub fn conjugate<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a0 = self.a0.clone();
        let a1 = self.a1.neg(&mut cs.namespace(|| "compute -a1 (conj)"))?;
        Ok(Self { a0, a1 })
    }

    pub fn square<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let mut cs = cs.namespace(|| "compute e2 square(x)");
        let a = self
            .a0
            .add(&mut cs.namespace(|| "a <- x.a0 + x.a1"), &self.a1)?;
        let b = self
            .a0
            .sub(&mut cs.namespace(|| "b <- x.a0 - x.a1"), &self.a1)?;
        let a = a.mul(&mut cs.namespace(|| "a <- a * b"), &b)?;

        let b = self
            .a0
            .mul(&mut cs.namespace(|| "b <- x.a0 * x.a1"), &self.a1)?;
        let b = b.mul_const(&mut cs.namespace(|| "b <- b * 2"), &BigInt::from(2))?;

        Ok(Self { a0: a, a1: b })
    }

    // FIXME: why not just mul_const directly and get rid of this function?
    pub fn double<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.mul_const(cs, &BigInt::from(2))
    }

    pub fn inverse<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let val = BlsFp2::from(self);
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

        let x = BlsFp2::from(self);

        let y = BlsFp2::from(value);
        if y.is_zero().into() {
            eprintln!("Inverse of zero element cannot be calculated");
            return Err(SynthesisError::DivisionByZero);
        }
        let y_inv = y.invert().unwrap();
        let div = y_inv.mul(&x);

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
        let a0 = AllocatedFieldElement::<F>::conditionally_select(
            &mut cs.namespace(|| "cond a0"),
            &z0.a0,
            &z1.a0,
            condition,
        )?;
        let a1 = AllocatedFieldElement::<F>::conditionally_select(
            &mut cs.namespace(|| "cond a1"),
            &z0.a1,
            &z1.a1,
            condition,
        )?;
        Ok(Self { a0, a1 })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use pasta_curves::Fp;

    use bls12_381::fp::Fp as BlsFp;

    #[test]
    fn test_random_add() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let b = BlsFp2::random(&mut rng);
        let c = &a + &b;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a+b"), &b_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a+b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 524);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_sub() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let b = BlsFp2::random(&mut rng);
        let c = &a - &b;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.sub(&mut cs.namespace(|| "a-b"), &b_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a-b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 524);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_double() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let c = &a + &a;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.double(&mut cs.namespace(|| "2a"));
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "2a = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 524);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_mul() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let b = BlsFp2::random(&mut rng);
        let c = &a * &b;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.mul(&mut cs.namespace(|| "a*b"), &b_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a*b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1355);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_mul_by_nonresidue() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let c = &a.mul_by_nonresidue();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.mul_by_nonresidue(&mut cs.namespace(|| "a*(1+u)"));
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a*(1+u) = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 524);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_square() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let c = &a * &a;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.square(&mut cs.namespace(|| "a²"));
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a² = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1347);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_div() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let mut b = BlsFp2::random(&mut rng);
        while b.invert().is_none().into() {
            b = BlsFp2::random(&mut rng);
        }
        let c = &a * &b.invert().unwrap();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.div_unchecked(&mut cs.namespace(|| "a div b"), &b_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a div b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1879);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_mul_element() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let b = BlsFp::random(&mut rng);
        let c = &a * &b.into();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_elem: AllocatedFieldElement<Fp> = (&b).into();
        let b_alloc = b_elem
            .0
            .allocate_field_element_unchecked(&mut cs.namespace(|| "alloc b"));
        assert!(b_alloc.is_ok());
        let _b_alloc = b_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.mul_element(&mut cs.namespace(|| "a*b (elm)"), &b_elem);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a*b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1310);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_mul_const() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        // the product can't overflow -- FIXME: can technically fail if the random is unlucky enough?
        let b = BlsFp::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x7f,
        ])
        .unwrap();
        let c = &a * &b.into();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let b_elem: AllocatedFieldElement<Fp> = (&b).into();
        let b_val: BigInt = (&b_elem.0).into();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.mul_const(&mut cs.namespace(|| "a*b (const)"), &b_val);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a*b = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 524);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_neg() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let c = -&a;

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.neg(&mut cs.namespace(|| "-a"));
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "-a = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 524);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_conjugate() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let c = &a.conjugate();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.conjugate(&mut cs.namespace(|| "conj(a)"));
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "conj(a) = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 524);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_inverse() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let c = &a.invert().unwrap_or_else(|| BlsFp2::zero());

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let res_alloc = a_alloc.inverse(&mut cs.namespace(|| "a^-1"));
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a^-1 = c"),
            &res_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1879);
        assert_eq!(cs.num_inputs(), 1);
    }

    #[test]
    fn test_random_alloc_is_zero() {
        let mut rng = rand::thread_rng();
        let a = BlsFp2::random(&mut rng);
        let b = BlsFp2::random(&mut rng);
        let c = b.clone();
        let zero = BlsFp2::zero();

        let mut cs = TestConstraintSystem::<Fp>::new();

        let a_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a"), &a);
        assert!(a_alloc.is_ok());
        let a_alloc = a_alloc.unwrap();

        let a2_alloc =
            AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc a2"), &a.neg());
        assert!(a2_alloc.is_ok());
        let a2_alloc = a2_alloc.unwrap();

        let b_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc b"), &b);
        assert!(b_alloc.is_ok());
        let b_alloc = b_alloc.unwrap();

        let res_alloc = a_alloc.add(&mut cs.namespace(|| "a-a"), &a2_alloc);
        assert!(res_alloc.is_ok());
        let res_alloc = res_alloc.unwrap();

        let c_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc c"), &c);
        assert!(c_alloc.is_ok());
        let c_alloc = c_alloc.unwrap();

        let z_alloc = AllocatedE2Element::alloc_element(&mut cs.namespace(|| "alloc zero"), &zero);
        assert!(z_alloc.is_ok());
        let z_alloc = z_alloc.unwrap();

        let z2_alloc = z_alloc.double(&mut cs.namespace(|| "z2 <- 2*z")).unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "a-a = z"),
            &res_alloc,
            &z2_alloc,
        );
        assert!(eq_alloc.is_ok());

        let zbit_alloc = res_alloc.alloc_is_zero(&mut cs.namespace(|| "z <- a-a ?= 0"));
        assert!(zbit_alloc.is_ok());
        let zbit_alloc = zbit_alloc.unwrap();

        let cond_alloc = AllocatedE2Element::conditionally_select(
            &mut cs.namespace(|| "select(a, b, z)"),
            &a_alloc,
            &b_alloc,
            &Boolean::Is(zbit_alloc),
        );
        assert!(cond_alloc.is_ok());
        let cond_alloc = cond_alloc.unwrap();

        let eq_alloc = AllocatedE2Element::assert_is_equal(
            &mut cs.namespace(|| "select(a, b, z) = c = b"),
            &cond_alloc,
            &c_alloc,
        );
        assert!(eq_alloc.is_ok());

        if !cs.is_satisfied() {
            eprintln!("{:?}", cs.which_is_unsatisfied())
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 2393);
        assert_eq!(cs.num_inputs(), 1);
    }
}
