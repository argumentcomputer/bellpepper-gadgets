use std::{
    borrow::Borrow,
    iter::{Product, Sum},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use num_bigint::{BigInt, RandBigInt, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};
use rand::RngCore;

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Fe25519(pub(crate) BigInt);

impl From<u64> for Fe25519 {
    fn from(value: u64) -> Self {
        Self(BigInt::from(value))
    }
}

impl From<BigInt> for Fe25519 {
    fn from(value: BigInt) -> Self {
        Self(value)
    }
}

impl Add<Self> for Fe25519 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self((&self.0 + &rhs.0).rem(Self::modulus()))
    }
}

impl AddAssign<Self> for Fe25519 {
    fn add_assign(&mut self, rhs: Self) {
        self.0 = (&self.0 + &rhs.0).rem(Self::modulus())
    }
}

impl<'a> Add<&'a Self> for Fe25519 {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self::Output {
        Self((&self.0 + &rhs.0).rem(Self::modulus()))
    }
}

impl<'a> Add<&'a Fe25519> for &Fe25519 {
    type Output = Fe25519;

    fn add(self, rhs: &'a Fe25519) -> Self::Output {
        Fe25519((self.0.clone() + rhs.0.clone()).rem(Fe25519::modulus()))
    }
}

impl<'a> AddAssign<&'a Self> for Fe25519 {
    fn add_assign(&mut self, rhs: &'a Self) {
        self.0 = (&self.0 + &rhs.0).rem(Self::modulus())
    }
}

impl Sub<Self> for Fe25519 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self((&self.0 + Self::modulus() - &rhs.0).rem(Self::modulus()))
    }
}

impl<'a> Sub<&'a Self> for Fe25519 {
    type Output = Self;

    fn sub(self, rhs: &'a Self) -> Self::Output {
        Self((&self.0 + Self::modulus() - &rhs.0).rem(Self::modulus()))
    }
}

impl SubAssign<Self> for Fe25519 {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = (&self.0 + Self::modulus() - &rhs.0).rem(Self::modulus())
    }
}

impl<'a> Sub<&'a Fe25519> for &Fe25519 {
    type Output = Fe25519;

    fn sub(self, rhs: &'a Fe25519) -> Self::Output {
        Fe25519((self.0.clone() + Fe25519::modulus() - rhs.0.clone()).rem(Fe25519::modulus()))
    }
}
impl<'a> SubAssign<&'a Self> for Fe25519 {
    fn sub_assign(&mut self, rhs: &'a Self) {
        self.0 = (&self.0 + Self::modulus() - &rhs.0).rem(Self::modulus())
    }
}

impl Mul<Self> for Fe25519 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self((&self.0 * &rhs.0).rem(Self::modulus()))
    }
}

impl<'a> Mul<&'a Self> for Fe25519 {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self::Output {
        Self((&self.0 * &rhs.0).rem(Self::modulus()))
    }
}

impl<'a> Mul<&'a Fe25519> for &Fe25519 {
    type Output = Fe25519;

    fn mul(self, rhs: &'a Fe25519) -> Self::Output {
        Fe25519((&self.0 * &rhs.0).rem(Fe25519::modulus()))
    }
}

impl<'a> MulAssign<&'a Self> for Fe25519 {
    fn mul_assign(&mut self, rhs: &'a Self) {
        self.0 = (&self.0 * &rhs.0).rem(Self::modulus())
    }
}

impl Neg for Fe25519 {
    type Output = Self;
    fn neg(self) -> Self::Output {
        let p = Self::modulus();
        Self(p - self.0)
    }
}

impl<'a> Neg for &'a Fe25519 {
    type Output = Fe25519;
    fn neg(self) -> Self::Output {
        let p = Fe25519::modulus();
        Fe25519(p - &self.0)
    }
}

impl<T> Sum<T> for Fe25519
where
    T: Borrow<Self>,
{
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, item| acc + item.borrow())
    }
}

impl<T> Product<T> for Fe25519
where
    T: Borrow<Self>,
{
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::one(), |acc, item| acc * item.borrow())
    }
}

impl Fe25519 {
    pub fn zero() -> Self {
        Self(BigInt::zero())
    }

    pub fn one() -> Self {
        Self(BigInt::one())
    }

    pub fn modulus() -> BigInt {
        BigInt::parse_bytes(
            b"7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed",
            16,
        )
        .unwrap()
    }

    pub fn sqrt_minus_one() -> Self {
        Self(
            BigInt::parse_bytes(
                b"2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0",
                16,
            )
            .unwrap(),
        )
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    pub fn random(mut rng: impl RngCore) -> Self {
        Self(rng.gen_bigint_range(&BigInt::zero(), &Self::modulus()))
    }

    pub fn square(&self) -> Self {
        let sq = &self.0 * &self.0;
        Self(sq.rem(Self::modulus()))
    }

    pub fn pow(&self, exponent: &BigInt) -> Self {
        let pw = self.0.modpow(exponent, &Self::modulus());
        Self(pw)
    }

    pub fn double(&self) -> Self {
        let dbl: BigInt = &self.0 << 1;
        Self(dbl.rem(Self::modulus()))
    }

    pub fn invert(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            let p = Self::modulus();
            let p_minus_2 = &p - BigInt::from(2);
            let inv = self.0.modpow(&p_minus_2, &p);
            Some(Self(inv))
        }
    }

    // https://www.rfc-editor.org/rfc/rfc8032#section-5.1.3
    pub fn sqrt(&self) -> Option<Self> {
        let exponent = (Self::modulus() + 3) / 8;
        let beta = self.pow(&exponent); // candidate square root

        let beta_sq = beta.square();
        let is_sq_root = (&beta_sq - self).is_zero() | (&beta_sq + self).is_zero();

        let neg_not_required = (&beta_sq - self).is_zero();
        let sq_root = if neg_not_required {
            beta
        } else {
            beta * Self::sqrt_minus_one()
        };

        if is_sq_root {
            Some(sq_root)
        } else {
            None
        }
    }

    pub fn is_even(&self) -> bool {
        self.0.is_even()
    }

    pub fn to_bytes_le(&self) -> [u8; 32] {
        let (_sign, bytes) = self.0.to_bytes_le();
        bytes
            .into_iter()
            .chain(vec![0u8; 31])
            .take(32)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn from_bytes_le(bytes: &[u8]) -> Self {
        Self(BigInt::from_bytes_le(Sign::Plus, bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanity_checks() {
        let two = Fe25519::from(2u64);
        let four = two.clone().mul(&two);
        let expected_four = Fe25519::from(4u64);

        assert_eq!(four, expected_four);
        assert_eq!(two.pow(&BigInt::from(2)), four);
        assert_eq!(two.square(), four);

        let two_inv = two.invert().unwrap();
        assert_eq!(two_inv * two, Fe25519::one());

        let sqrt_m1 = Fe25519::sqrt_minus_one();
        assert_eq!(sqrt_m1.square(), -Fe25519::one());
    }

    #[test]
    fn check_add_sub() {
        let mut rng = rand::thread_rng();
        let mut x = Fe25519::random(&mut rng);
        let y = Fe25519::random(&mut rng);
        let neg_y = -&y;
        assert_eq!(&y + &neg_y, Fe25519::zero());
        assert_eq!(&x + &neg_y, &x - &y);

        let old_x = x.clone();
        x -= &y;
        assert_eq!(&x + &y, old_x);
        x += &y;
        assert_eq!(x, old_x);

        let a = [
            x.clone(),
            Fe25519::from(1u64),
            Fe25519::from(2u64),
            y.clone(),
        ];
        assert_eq!(Fe25519::sum(a.iter()), &x + &y + Fe25519::from(3u64));

        let y_ref = &y;
        assert_eq!(&x + &y, &x + y_ref);
        x += y_ref;
        assert_eq!(&x - &y, &x - y_ref);
        x -= y_ref;
        assert_eq!(&x + &y, &x + y_ref);
    }

    #[test]
    fn check_mul() {
        let mut rng = rand::thread_rng();
        let mut x = Fe25519::random(&mut rng);
        let y = Fe25519::random(&mut rng);
        assert_eq!(x.invert().unwrap() * &x, Fe25519::one());

        let old_x = x.clone();
        x *= &y;
        assert_eq!(&x * &y.invert().unwrap(), old_x);

        let a = [
            x.clone(),
            Fe25519::from(2u64),
            Fe25519::from(3u64),
            y.clone(),
        ];
        assert_eq!(Fe25519::product(a.iter()), &x * &y * Fe25519::from(6u64));

        let y_ref = &y;
        assert_eq!(&x * &y, &x * y_ref);
        x *= y_ref;
        assert_eq!(&x * &y.invert().unwrap(), x * y_ref.invert().unwrap());
    }

    #[test]
    fn check_square_double() {
        let mut rng = rand::thread_rng();
        let x = Fe25519::random(&mut rng);
        assert_eq!(x.square(), &x * &x);
        assert_eq!(x.double(), &x + &x);
        let two = Fe25519::from(2u64);
        assert_eq!(x.double(), x * two);
    }

    #[test]
    fn check_square_root() {
        let two = Fe25519::from(2u64);
        assert!(two.sqrt().is_none());

        let four = two.square();
        let sq_root_opt = Fe25519::sqrt(&four);
        assert!(sq_root_opt.is_some());
        let sq_root = sq_root_opt.unwrap();
        assert!(sq_root == two || sq_root == -two);

        let mut rng = rand::thread_rng();
        let x = Fe25519::random(&mut rng);
        let x_sq = x.square();
        let sq_root_opt = Fe25519::sqrt(&x_sq);
        assert!(sq_root_opt.is_some());
        let sq_root = sq_root_opt.unwrap();
        assert!(sq_root == x || sq_root == -x);
        assert_eq!(sq_root.square(), x_sq);
    }
}
