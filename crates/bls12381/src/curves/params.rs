use std::marker::PhantomData;




use ff::{PrimeField, PrimeFieldBits};

use crate::fields::{e2::AllocatedE2Element, fp::AllocatedFieldElement};

// TODO: add the following if we need them:
// Gm: m*base point coords
// Eigenvalue: endomorphism eigenvalue
// ThirdRootOne: endomorphism image scaler

// TODO: add trait bounds on BaseElement so generic curve operations can be shared between curves
// CurveParams defines parameters of an elliptic curve in short Weierstrass form
// given by the equation
//
//      Y² = X³ + aX + b
//
// The base point is defined by generator()
pub trait EmulatedCurveParams<BaseElement> {
    fn a() -> BaseElement;
    fn b() -> BaseElement;

    fn generator() -> (BaseElement, BaseElement); // returns (x, y) coordinates of a generator point for the curve
}

pub trait EmulatedCurve<Params: EmulatedCurveParams<BaseElement>, BaseElement> {
    // ....
}

pub struct Bls12381G1Params<F> {
    _f: PhantomData<F>,
}

pub struct Bls12381G2Params<F> {
    _f: PhantomData<F>,
}

impl<F: PrimeField + PrimeFieldBits> EmulatedCurveParams<AllocatedFieldElement<F>>
    for Bls12381G1Params<F>
{
    fn a() -> AllocatedFieldElement<F> {
        AllocatedFieldElement::<F>::zero()
    }

    fn b() -> AllocatedFieldElement<F> {
        AllocatedFieldElement::<F>::from_dec("4").unwrap()
    }

    fn generator() -> (AllocatedFieldElement<F>, AllocatedFieldElement<F>) {
        // https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-10.html#name-bls-curves-for-the-128-bit-
        let x = AllocatedFieldElement::<F>::from_dec("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507").unwrap();
        let y = AllocatedFieldElement::<F>::from_dec("1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569").unwrap();
        (x, y)
    }
}

impl<F: PrimeField + PrimeFieldBits> EmulatedCurveParams<AllocatedE2Element<F>>
    for Bls12381G2Params<F>
{
    fn a() -> AllocatedE2Element<F> {
        AllocatedE2Element::<F>::zero()
    }

    fn b() -> AllocatedE2Element<F> {
        // 4*(u + 1) becomes (4, 4)
        AllocatedE2Element::<F>::from_dec(("4", "4")).unwrap()
    }

    fn generator() -> (AllocatedE2Element<F>, AllocatedE2Element<F>) {
        // https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-10.html#name-bls-curves-for-the-128-bit-
        let x = AllocatedE2Element::<F>::from_dec(("352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160", "3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758")).unwrap();
        let y = AllocatedE2Element::<F>::from_dec(("1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905", "927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582")).unwrap();
        (x, y)
    }
}

impl<F: PrimeField + PrimeFieldBits> Bls12381G2Params<F> {
    pub fn u1() -> AllocatedFieldElement<F> {
        AllocatedFieldElement::<F>::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437").unwrap()
    }

    pub fn v() -> AllocatedE2Element<F> {
        AllocatedE2Element::<F>::from_dec(("2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530", "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257")).unwrap()
    }
}

impl<F: PrimeField + PrimeFieldBits> Bls12381G1Params<F> {
    pub fn w() -> AllocatedFieldElement<F> {
        AllocatedFieldElement::<F>::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()
    }
}
