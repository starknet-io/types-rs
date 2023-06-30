#![cfg_attr(not(feature = "std"), no_std)]

use bitvec::array::BitArray;

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
    pub const ONE: Self = Self(FieldElement::<Stark252PrimeField>::const_from_raw(
        UnsignedInteger::from_u64(1),
    ));

    /// [Felt] constant that's equal to 2.
    pub const TWO: Self = Self(FieldElement::<Stark252PrimeField>::const_from_raw(
        UnsignedInteger::from_u64(2),
    ));

    /// [Felt] constant that's equal to 3.
    pub const THREE: Self = Self(FieldElement::<Stark252PrimeField>::const_from_raw(
        UnsignedInteger::from_u64(3),
    ));

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
    pub fn floor_div(&self, _rhs: &NonZeroFelt) -> Self {
        todo!()
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
    pub fn mul_mod(&self, _rhs: &Self, _p: &Self) -> Self {
        todo!()
    }

    /// Modular multiplicative inverse.
    pub const fn inverse_mod(&self, _p: &Self) -> Self {
        todo!()
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
