#![cfg_attr(not(feature = "std"), no_std)]

use bitvec::array::BitArray;

#[cfg(test)]
mod arbitrary;

#[cfg(target_pointer_width = "64")]
pub type BitArrayStore = [u64; 4];

#[cfg(not(target_pointer_width = "64"))]
pub type BitArrayStore = [u32; 8];

use lambdaworks_math::{
    field::{
        element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
    },
    traits::ByteConversion,
    unsigned_integer::element::UnsignedInteger,
};

/// Definition of the Field Element type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Felt(FieldElement<Stark252PrimeField>);

/// A non-zero [Felt].
pub struct NonZeroFelt(FieldElement<Stark252PrimeField>);

#[derive(Debug)]
pub struct FeltIsZeroError;

#[derive(Debug)]
pub struct FromStrError;

#[derive(Debug)]
pub struct FromBytesError;

impl Felt {
    /// [Felt] constant that's equal to 0.
    pub const ZERO: Self = Self(FieldElement::<Stark252PrimeField>::const_from_raw(
        UnsignedInteger::from_u64(0),
    ));

    /// [Felt] constant that's equal to 1.
    pub const ONE: Self = Self(FieldElement::<Stark252PrimeField>::from_hex_unchecked("1"));

    /// [Felt] constant that's equal to 2.
    pub const TWO: Self = Self(FieldElement::<Stark252PrimeField>::from_hex_unchecked("2"));

    /// [Felt] constant that's equal to 3.
    pub const THREE: Self = Self(FieldElement::<Stark252PrimeField>::from_hex_unchecked("3"));

    /// Maximum value of [Felt]. Equals to 2^251 + 17 * 2^192.
    pub const MAX: Self = Self(FieldElement::<Stark252PrimeField>::const_from_raw(
        UnsignedInteger::from_limbs([544, 0, 0, 32]),
    ));

    /// Creates a new [Felt] from its big-endian representation in a [u8] slice.
    pub fn from_bytes_be(bytes: &[u8]) -> Result<Self, FromBytesError> {
        FieldElement::from_bytes_be(bytes)
            .map(Self)
            .map_err(|_| FromBytesError)
    }

    /// Creates a new [Felt] from its little-endian representation in a [u8] slice.
    pub fn from_bytes_le(bytes: &[u8]) -> Result<Self, FromBytesError> {
        FieldElement::from_bytes_le(bytes)
            .map(Self)
            .map_err(|_| FromBytesError)
    }

    /// Converts to big-endian byte representation in a [u8] array.
    pub fn to_bytes_be(&self) -> [u8; 32] {
        self.0.to_bytes_be()
    }

    /// Converts to little-endian byte representation in a [u8] array.
    pub fn to_bytes_le(&self) -> [u8; 32] {
        self.0.to_bytes_le()
    }

    /// Converts to big-endian bit representation.
    pub fn to_bits_be(&self) -> BitArray<BitArrayStore> {
        let mut limbs = self.0.representative().limbs;
        limbs.reverse();
        #[cfg(not(target_pointer_width = "64"))]
        let limbs: [u32; 8] = limbs
            .map(|n| [(n >> 32) as u32, n as u32])
            .into_iter()
            .flatten()
            .collect::<Vec<u32>>()
            .try_into()
            .unwrap();

        BitArray::new(limbs)
    }

    /// Converts to little-endian bit representation.
    pub fn to_bits_le(&self) -> BitArray<BitArrayStore> {
        let limbs = self.0.representative().limbs;

        #[cfg(not(target_pointer_width = "64"))]
        let limbs: [u32; 8] = limbs
            .map(|n| [n as u32, n >> 32 as u32])
            .into_iter()
            .flatten()
            .collect::<Vec<u32>>()
            .try_into()
            .unwrap();

        BitArray::new(limbs)
    }

    /// Checks if `self` is equal to [Felt::Zero].
    pub fn is_zero(&self) -> bool {
        self.0 == FieldElement::<Stark252PrimeField>::zero()
    }
    /// Finite field division.
    pub fn field_div(&self, rhs: &NonZeroFelt) -> Self {
        Self(self.0 / rhs.0)
    }

    /// Floor division.
    pub fn floor_div(&self, rhs: &NonZeroFelt) -> Self {
        Self::from_bytes_be(
            &(self.0.representative().div_rem(&rhs.0.representative()))
                .0
                .to_bytes_be(),
        )
        .unwrap_or_default()
    }

    /// Multiplicative inverse.
    pub fn inverse(&self) -> Option<Self> {
        Some(Self(self.0.inv()))
    }

    /// Finds the square root. There may be 2 roots for each square, and the lower one is returned.
    pub fn sqrt(&self) -> Option<Self> {
        let (root_1, root_2) = self.0.sqrt()?;
        Some(Self(if root_1 < root_2 { root_1 } else { root_2 }))
    }

    /// Raises `self` to the power of 2.
    pub fn square(&self) -> Self {
        Self(self.0.square())
    }

    /// Raises `self` to the power of `exponent`.
    pub fn pow(&self, exponent: u128) -> Self {
        Self(self.0.pow(exponent))
    }

    /// Modular multiplication.
    pub fn mul_mod(&self, rhs: &Self, p: &Self) -> Self {
        Self::from_bytes_be(
            &(self.0 * rhs.0)
                .representative()
                .div_rem(&p.0.representative())
                .1
                .to_bytes_be(),
        )
        .unwrap_or_default()
    }

    /// Modular multiplicative inverse.
    pub fn inverse_mod(&self, p: &Self) -> Self {
        Self::from_bytes_be(
            &self
                .0
                .inv()
                .representative()
                .div_rem(&p.0.representative())
                .1
                .to_bytes_be(),
        )
        .unwrap_or_default()
    }
}

/// Defaults to [Felt::ZERO].
impl Default for Felt {
    fn default() -> Self {
        Self(FieldElement::<Stark252PrimeField>::zero())
    }
}

impl AsRef<Felt> for Felt {
    fn as_ref(&self) -> &Felt {
        self
    }
}

impl From<NonZeroFelt> for Felt {
    fn from(value: NonZeroFelt) -> Self {
        Self(value.0)
    }
}

impl From<&NonZeroFelt> for Felt {
    fn from(value: &NonZeroFelt) -> Self {
        Self(value.0)
    }
}

impl AsRef<NonZeroFelt> for NonZeroFelt {
    fn as_ref(&self) -> &NonZeroFelt {
        self
    }
}

impl TryFrom<Felt> for NonZeroFelt {
    type Error = FeltIsZeroError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        if value.is_zero() {
            Err(FeltIsZeroError)
        } else {
            Ok(Self(value.0))
        }
    }
}

impl TryFrom<&Felt> for NonZeroFelt {
    type Error = FeltIsZeroError;

    fn try_from(value: &Felt) -> Result<Self, Self::Error> {
        if value.is_zero() {
            Err(FeltIsZeroError)
        } else {
            Ok(Self(value.0))
        }
    }
}

mod arithmetic {
    use core::{iter, ops};

    use super::*;

    /// Field addition. Never overflows/underflows.
    impl ops::AddAssign<Felt> for Felt {
        fn add_assign(&mut self, rhs: Felt) {
            self.0 += rhs.0
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::AddAssign<&Felt> for Felt {
        fn add_assign(&mut self, rhs: &Felt) {
            self.0 += rhs.0
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<Felt> for Felt {
        type Output = Felt;

        fn add(self, rhs: Felt) -> Self::Output {
            Self(self.0 + rhs.0)
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<&Felt> for Felt {
        type Output = Felt;

        fn add(self, rhs: &Felt) -> Self::Output {
            Self(self.0 + rhs.0)
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<Felt> for &Felt {
        type Output = Felt;

        fn add(self, rhs: Felt) -> Self::Output {
            Felt(self.0 + rhs.0)
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<&Felt> for &Felt {
        type Output = Felt;

        fn add(self, rhs: &Felt) -> Self::Output {
            Felt(self.0 + rhs.0)
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::SubAssign<Felt> for Felt {
        fn sub_assign(&mut self, rhs: Felt) {
            self.0 = self.0 - rhs.0
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::SubAssign<&Felt> for Felt {
        fn sub_assign(&mut self, rhs: &Felt) {
            self.0 = self.0 - rhs.0
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<Felt> for Felt {
        type Output = Felt;

        fn sub(self, rhs: Felt) -> Self::Output {
            Self(self.0 - rhs.0)
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<&Felt> for Felt {
        type Output = Felt;

        fn sub(self, rhs: &Felt) -> Self::Output {
            Self(self.0 - rhs.0)
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<Felt> for &Felt {
        type Output = Felt;

        fn sub(self, rhs: Felt) -> Self::Output {
            Felt(self.0 - rhs.0)
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<&Felt> for &Felt {
        type Output = Felt;

        fn sub(self, rhs: &Felt) -> Self::Output {
            Felt(self.0 - rhs.0)
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::MulAssign<Felt> for Felt {
        fn mul_assign(&mut self, rhs: Felt) {
            self.0 = self.0 * rhs.0
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::MulAssign<&Felt> for Felt {
        fn mul_assign(&mut self, rhs: &Felt) {
            self.0 = self.0 * rhs.0
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::Mul<Felt> for Felt {
        type Output = Felt;

        fn mul(self, rhs: Felt) -> Self::Output {
            Self(self.0 * rhs.0)
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::Mul<&Felt> for Felt {
        type Output = Felt;

        fn mul(self, rhs: &Felt) -> Self::Output {
            Self(self.0 * rhs.0)
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::Mul<Felt> for &Felt {
        type Output = Felt;

        fn mul(self, rhs: Felt) -> Self::Output {
            Felt(self.0 * rhs.0)
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::Mul<&Felt> for &Felt {
        type Output = Felt;

        fn mul(self, rhs: &Felt) -> Self::Output {
            Felt(self.0 * rhs.0)
        }
    }

    // [ops::Div] not implemented by design to prevent misuse. Use [Felt::floor_div] or
    // [Felt::field_div] instead.

    impl ops::Neg for Felt {
        type Output = Felt;

        fn neg(self) -> Self::Output {
            Self(self.0.neg())
        }
    }

    impl ops::Neg for &Felt {
        type Output = Felt;

        fn neg(self) -> Self::Output {
            Felt(self.0.neg())
        }
    }

    impl iter::Sum for Felt {
        fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.sum()
        }
    }

    impl<'a> iter::Sum<&'a Felt> for Felt {
        fn sum<I: Iterator<Item = &'a Felt>>(iter: I) -> Self {
            iter.sum()
        }
    }
}

#[cfg(feature = "serde")]
mod serde {
    use core::fmt;

    use ::serde::{de, Deserialize, Serialize};

    use super::*;

    impl Serialize for Felt {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: ::serde::Serializer,
        {
            serializer.serialize_str(&self.to_string())
        }
    }

    impl<'de> Deserialize<'de> for Felt {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: ::serde::Deserializer<'de>,
        {
            deserializer.deserialize_str(FeltVisitor)
        }
    }

    struct FeltVisitor;

    impl<'de> de::Visitor<'de> for FeltVisitor {
        type Value = Felt;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("Failed to deserialize hexadecimal string")
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            // Strip the '0x' prefix from the encoded hex string
            if let Some(no_prefix_hex) = value.strip_prefix("0x") {
                Ok(Felt(FieldElement::<Stark252PrimeField>::const_from_raw(
                    UnsignedInteger::from(no_prefix_hex),
                )))
            } else {
                Err(String::from("Extected hex string to be prefixed by '0x'"))
                    .map_err(de::Error::custom)
            }
        }
    }
}

mod formatting {
    use core::fmt;

    use super::*;

    /// Represents [Felt] in decimal by default.
    impl fmt::Display for Felt {
        fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
            todo!()
        }
    }

    /// Represents [Felt] in lowercase hexadecimal format.
    impl fmt::LowerHex for Felt {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Display::fmt(&self.0, f)
        }
    }

    /// Represents [Felt] in uppercase hexadecimal format.
    impl fmt::UpperHex for Felt {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.0.to_string().to_uppercase())
        }
    }
}

mod errors {
    use core::fmt;

    use super::*;

    #[cfg(feature = "std")]
    impl std::error::Error for FeltIsZeroError {}

    impl fmt::Display for FeltIsZeroError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            "Tried to create NonZeroFelt from 0".fmt(f)
        }
    }

    #[cfg(feature = "std")]
    impl std::error::Error for FromStrError {}

    impl fmt::Display for FromStrError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            "Failed to create Felt from string".fmt(f)
        }
    }

    #[cfg(feature = "std")]
    impl std::error::Error for FromBytesError {}

    impl fmt::Display for FromBytesError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            "Failed to create Felt from bytes".fmt(f)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::arbitrary::nonzero_felt;

    use super::*;

    use proptest::prelude::*;

    proptest! {
        #[test]
        // Property-based test that ensures, for 100 felt values that are randomly generated
        // each time tests are run, that a new felt doesn't fall outside the range [0, p].
        // In this and some of the following tests, The value of {x} can be either [0] or a
        // very large number, in order to try to overflow the value of {p} and thus ensure the
        // modular arithmetic is working correctly.
        fn new_in_range(ref x in any::<[u8; 40]>()) {
            let x = Felt::from_bytes_be(x).unwrap();
            prop_assert!(x < Felt::MAX);
        }

        #[test]
        fn to_be_bytes(ref x in any::<Felt>()) {
            let bytes = x.to_bytes_be();
            let y = &Felt::from_bytes_be(&bytes).unwrap();
            prop_assert_eq!(x, y);
        }

        #[test]
        fn to_le_bytes(ref x in any::<Felt>()) {
            let bytes = x.to_bytes_le();
            let y = &Felt::from_bytes_le(&bytes).unwrap();
            prop_assert_eq!(x, y);
        }

        #[test]
        fn to_bits_be(ref x in any::<Felt>()) {
            let bits: Vec<bool> = x.to_bits_be().into_iter().rev().collect();
            let mut res = [0;32];
            let mut acc: u8 = 0;
            for (i, bits64) in bits.chunks(8).enumerate() {
                for bit in bits64.iter() {
                    acc <<= 1;
                    acc += *bit as u8;
                }
                res[i] = acc;
                acc = 0;
            }
            let y = &Felt::from_bytes_be(&res).unwrap();
            prop_assert_eq!(x, y);
        }

        #[test]
        fn to_bits_le(ref x in any::<Felt>()) {
            let bits: Vec<bool> = x.to_bits_le().into_iter().collect();
            let mut res = [0;4];
            let mut acc: u64 = 0;
            for (i, bits64) in bits.chunks(64).enumerate() {
                for bit in bits64.iter().rev() {
                    acc <<= 1;
                    acc += *bit as u64;
                }
                res[i] = acc;
                acc = 0;
            }
            let mut bytes = [0u8; 32];
            for i in (0..4).rev() {
                let limb_bytes = res[i].to_le_bytes();
                for j in 0..8 {
                    bytes[(3 - i) * 8 + j] = limb_bytes[j]
                }
            }
            let y = &Felt::from_bytes_le(&bytes).unwrap();
            prop_assert_eq!(x, y);
        }

        #[test]
        // Property-based test that ensures, for 100 felt values that are randomly
        // generated each time tests are run, that a felt created using Felt252::from_bytes_be doesn't
        // fall outside the range [0, p].
        // In this and some of the following tests, The value of {x} can be either [0] or a very large number,
        // in order to try to overflow the value of {p} and thus ensure the modular arithmetic is working correctly.
        fn from_bytes_be_in_range(ref x in any::<[u8; 40]>()) {
            let x = Felt::from_bytes_be(x).unwrap();
            prop_assert!(x <= Felt::MAX);
        }

        #[test]
        // Property-based test that ensures, for 100 felt values that are randomly generated each time
        // tests are run, that the negative of a felt doesn't fall outside the range [0, p].
        fn neg_in_range(x in any::<Felt>()) {
            prop_assert!(-x <= Felt::MAX);
        }

        #[test]
        // Property-based test that ensures, for 100 {x} and {y} values that are randomly generated
        // each time tests are run, that a subtraction between two felts {x} and {y} and doesn't fall
        // outside the range [0, p]. The values of {x} and {y} can be either [0] or a very large number.
        fn sub(ref x in any::<Felt>(), ref y in any::<Felt>()) {
            // x - y
            prop_assert!(x - y <= Felt::MAX);
            prop_assert_eq!(Felt::MAX + x - y + Felt::ONE, x - y);
            // y - x
            prop_assert!(y - x <= Felt::MAX);
            prop_assert_eq!(Felt::MAX + y - x + Felt::ONE, y - x);
        }

        #[test]
        // Property-based test that ensures, for 100 {x} and {y} values that are randomly generated
        // each time tests are run, that a subtraction with assignment between two felts {x} and {y}
        // and doesn't fall outside the range [0, p]. The values of {x} and {y} can be either [0] or a very large number.
        fn sub_assign_in_range(mut x in any::<Felt>(), y in any::<Felt>()) {
            x -= y;
            prop_assert!(x <= Felt::MAX);
            // test reference variant
            x -= &y;
            prop_assert!(x <= Felt::MAX);
        }

        #[test]
        // Property-based test that ensures, for 100 {x} and {y} values that are randomly
        // generated each time tests are run, that a multiplication between two felts {x}
        // and {y} and doesn't fall outside the range [0, p]. The values of {x} and {y}
        // can be either [0] or a very large number.
        fn mul(ref x in any::<Felt>(), ref y in any::<Felt>()) {
            prop_assert_eq!(x * y, y * x);
            prop_assert!(x * y <= Felt::MAX);
        }

        #[test]
        // Property-based test that ensures, for 100 pairs of {x} and {y} values that
        // are randomly generated each time tests are run, that a multiplication with
        // assignment between two felts {x} and {y} and doesn't fall outside the range [0, p].
        // The values of {x} and {y} can be either [0] or a very large number.
        fn mul_assign_in_range(mut x in any::<Felt>(), y in any::<Felt>()) {
            x *= y;
            prop_assert!(x <= Felt::MAX);
            // test reference variant
            x *= &y;
            prop_assert!(x <= Felt::MAX);
        }

        #[test]
        // Property-based test that ensures, for 100 pairs of {x} and {y} values that are
        // randomly generated each time tests are run, that the result of the division of
        // {x} by {y} is the inverse multiplicative of {x} --that is, multiplying the result
        // by {y} returns the original number {x}. The values of {x} and {y} can be either
        // [0] or a very large number.
        fn field_div_is_mul_inv(x in any::<Felt>(), y in nonzero_felt()) {
            let q = x.field_div(&NonZeroFelt(y.0));
            prop_assert!(q <= Felt::MAX);
            prop_assert_eq!(q * y, x);
        }

        #[test]
        // Property-based test that ensures, for 100 values {x} that are randomly
        // generated each time tests are run, that raising {x} to the {y}th power
        // returns a result that is inside of the range [0, p].
        fn pow_in_range(base in any::<Felt>(), exp in 0..u128::MAX){
            prop_assert!(base.pow(exp) <= Felt::MAX);
        }

        #[test]
        // Property based test that ensures, for 100 pairs of values {x} and {y}
        // generated at random each time tests are run, that performing an Add operation
        // between them returns a result that is inside of the range [0, p].
        fn add_in_range(x in any::<Felt>(), y in any::<Felt>()){
            prop_assert!(x + y <= Felt::MAX);
        }

        /// Tests the additive identity of the implementation of Zero trait for felts
        ///
        /// ```{.text}
        /// x + 0 = x       ∀ x
        /// 0 + x = x       ∀ x
        /// ```
        #[test]
        fn zero_additive_identity(x in any::<Felt>()) {
            prop_assert_eq!(x, x + Felt::ZERO);
            prop_assert_eq!(x, Felt::ZERO + x);
        }

        /// Tests the multiplicative identity of the implementation of One trait for felts
        ///
        /// ```{.text}
        /// x * 1 = x       ∀ x
        /// 1 * x = x       ∀ x
        /// ```
        #[test]
        fn one_multiplicative_identity(x in any::<Felt>()) {
            prop_assert_eq!(x, x * Felt::ONE);
            prop_assert_eq!(x, Felt::ONE * x);
        }

        #[test]
        fn sqrt_in_range(x in any::<Felt>()) {
            // we use x = x' * x' so x has a square root
            prop_assert!((x * x).sqrt().unwrap() <= Felt::MAX);
        }
    }
}
