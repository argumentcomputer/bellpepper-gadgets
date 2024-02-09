use std::marker::PhantomData;

use ff::{PrimeField, PrimeFieldBits};

use crate::fields::{fp::FpElement, fp2::Fp2Element};

pub trait EmulatedCurveParams<BaseElement> {
    fn a() -> BaseElement;
    fn b() -> BaseElement;

    fn generator() -> (BaseElement, BaseElement); // returns (x, y) coordinates of a generator point for the curve
}

pub struct Bls12381G1Params<F> {
    _f: PhantomData<F>,
}

pub struct Bls12381G2Params<F> {
    _f: PhantomData<F>,
}

impl<F: PrimeField + PrimeFieldBits> EmulatedCurveParams<FpElement<F>> for Bls12381G1Params<F> {
    fn a() -> FpElement<F> {
        FpElement::<F>::zero()
    }

    fn b() -> FpElement<F> {
        FpElement::<F>::from_dec("4").unwrap()
    }

    fn generator() -> (FpElement<F>, FpElement<F>) {
        // https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-10.html#name-bls-curves-for-the-128-bit-
        let x = FpElement::<F>::from_dec("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507").unwrap();
        let y = FpElement::<F>::from_dec("1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569").unwrap();
        (x, y)
    }
}

impl<F: PrimeField + PrimeFieldBits> EmulatedCurveParams<Fp2Element<F>> for Bls12381G2Params<F> {
    fn a() -> Fp2Element<F> {
        Fp2Element::<F>::zero()
    }

    fn b() -> Fp2Element<F> {
        // 4*(u + 1) becomes (4, 4)
        Fp2Element::<F>::from_dec(("4", "4")).unwrap()
    }

    fn generator() -> (Fp2Element<F>, Fp2Element<F>) {
        // https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-10.html#name-bls-curves-for-the-128-bit-
        let x = Fp2Element::<F>::from_dec(("352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160", "3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758")).unwrap();
        let y = Fp2Element::<F>::from_dec(("1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905", "927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582")).unwrap();
        (x, y)
    }
}

impl<F: PrimeField + PrimeFieldBits> Bls12381G2Params<F> {
    pub fn c0() -> Fp2Element<F> {
        Fp2Element::<F>::from_dec(("0", "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437")).unwrap()
    }

    pub fn c1() -> Fp2Element<F> {
        Fp2Element::<F>::from_dec(("2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530", "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257")).unwrap()
    }

    /// Third root of unity
    pub fn w() -> FpElement<F> {
        FpElement::<F>::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()
    }
}

impl<F: PrimeField + PrimeFieldBits> Bls12381G1Params<F> {
    /// Third root of unity
    pub fn w() -> FpElement<F> {
        FpElement::<F>::from_dec("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()
    }
}
