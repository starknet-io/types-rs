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
    unsigned_integer::element::UnsignedInteger,
};

/// Definition of the Field Element type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Felt(FieldElement<Stark252PrimeField>);

/// A non-zero [Felt].
pub struct NonZeroFelt {}

#[derive(Debug)]
pub struct FeltIsZeroError;

#[derive(Debug)]
pub struct FromStrError;

#[derive(Debug)]
pub struct FromBytesError;

impl Felt {
    /// [Felt] constant that's equal to 0.
    pub const ZERO: Self = Self {};

    /// [Felt] constant that's equal to 1.
    pub const ONE: Self = Self {};

    /// [Felt] constant that's equal to 2.
    pub const TWO: Self = Self {};

    /// [Felt] constant that's equal to 3.
    pub const THREE: Self = Self {};

    /// Maximum value of [Felt]. Equals to 2^251 + 17 * 2^192.
    pub const MAX: Self = Self {};

    /// Creates a new [Felt] from its big-endian representation in a [u8] slice.
    pub const fn from_bytes_be(_bytes: &[u8]) -> Result<Self, FromBytesError> {
        todo!()
    }

    /// Creates a new [Felt] from its little-endian representation in a [u8] slice.
    pub const fn from_bytes_le(_bytes: &[u8]) -> Result<Self, FromBytesError> {
        todo!()
    }

    /// Converts to big-endian byte representation in a [u8] array.
    pub const fn to_bytes_be(&self) -> [u8; 32] {
        todo!()
    }

    /// Converts to little-endian byte representation in a [u8] array.
    pub const fn to_bytes_le(&self) -> [u8; 32] {
        todo!()
    }

    /// Converts to big-endian bit representation.
    pub const fn to_bits_be(&self) -> BitArray<BitArrayStore> {
        todo!()
    }

    /// Converts to little-endian bit representation.
    pub const fn to_bits_le(&self) -> BitArray<BitArrayStore> {
        todo!()
    }

    /// Checks if `self` is equal to [Felt::Zero].
    pub const fn is_zero(&self) -> bool {
        todo!()
    }

    /// Finite field division.
    pub const fn field_div(&self, _rhs: &NonZeroFelt) -> Self {
        todo!()
    }

    /// Floor division.
    pub const fn floor_div(&self, _rhs: &NonZeroFelt) -> Self {
        todo!()
    }

    /// Multiplicative inverse.
    pub const fn inverse(&self) -> Option<Self> {
        todo!()
    }

    /// Finds the square root. There may be 2 roots for each square, and the lower one is returned.
    pub const fn sqrt(&self) -> Option<Self> {
        todo!()
    }

    /// Raises `self` to the power of 2.
    pub const fn square(&self) -> Self {
        todo!()
    }

    /// Raises `self` to the power of `exponent`.
    pub const fn pow(&self, _exponent: u128) -> Self {
        todo!()
    }

    /// Modular multiplication.
    pub const fn mul_mod(&self, _rhs: &Self, _p: &Self) -> Self {
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
        todo!()
    }
}

impl AsRef<Felt> for Felt {
    fn as_ref(&self) -> &Felt {
        todo!()
    }
}

impl From<NonZeroFelt> for Felt {
    fn from(_value: NonZeroFelt) -> Self {
        todo!()
    }
}

impl From<&NonZeroFelt> for Felt {
    fn from(_value: &NonZeroFelt) -> Self {
        todo!()
    }
}

impl AsRef<NonZeroFelt> for NonZeroFelt {
    fn as_ref(&self) -> &NonZeroFelt {
        todo!()
    }
}

impl TryFrom<Felt> for NonZeroFelt {
    type Error = NonZeroFelt;

    fn try_from(_value: Felt) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl TryFrom<&Felt> for NonZeroFelt {
    type Error = NonZeroFelt;

    fn try_from(_value: &Felt) -> Result<Self, Self::Error> {
        todo!()
    }
}

mod arithmetic {
    use core::{iter, ops};

    use super::*;

    /// Field addition. Never overflows/underflows.
    impl ops::AddAssign<Felt> for Felt {
        fn add_assign(&mut self, _rhs: Felt) {
            todo!()
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::AddAssign<&Felt> for Felt {
        fn add_assign(&mut self, _rhs: &Felt) {
            todo!()
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<Felt> for Felt {
        type Output = Felt;

        fn add(self, _rhs: Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<&Felt> for Felt {
        type Output = Felt;

        fn add(self, _rhs: &Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<Felt> for &Felt {
        type Output = Felt;

        fn add(self, _rhs: Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<&Felt> for &Felt {
        type Output = Felt;

        fn add(self, _rhs: &Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::SubAssign<Felt> for Felt {
        fn sub_assign(&mut self, _rhs: Felt) {
            todo!()
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::SubAssign<&Felt> for Felt {
        fn sub_assign(&mut self, _rhs: &Felt) {
            todo!()
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<Felt> for Felt {
        type Output = Felt;

        fn sub(self, _rhs: Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<&Felt> for Felt {
        type Output = Felt;

        fn sub(self, _rhs: &Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<Felt> for &Felt {
        type Output = Felt;

        fn sub(self, _rhs: Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<&Felt> for &Felt {
        type Output = Felt;

        fn sub(self, _rhs: &Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::MulAssign<Felt> for Felt {
        fn mul_assign(&mut self, _rhs: Felt) {
            todo!()
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::MulAssign<&Felt> for Felt {
        fn mul_assign(&mut self, _rhs: &Felt) {
            todo!()
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::Mul<Felt> for Felt {
        type Output = Felt;

        fn mul(self, _rhs: Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::Mul<&Felt> for Felt {
        type Output = Felt;

        fn mul(self, _rhs: &Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::Mul<Felt> for &Felt {
        type Output = Felt;

        fn mul(self, _rhs: Felt) -> Self::Output {
            todo!()
        }
    }

    /// Field multiplication. Never overflows/underflows.
    impl ops::Mul<&Felt> for &Felt {
        type Output = Felt;

        fn mul(self, _rhs: &Felt) -> Self::Output {
            todo!()
        }
    }

    // [ops::Div] not implemented by design to prevent misuse. Use [Felt::floor_div] or
    // [Felt::field_div] instead.

    impl ops::Neg for Felt {
        type Output = Felt;

        fn neg(self) -> Self::Output {
            todo!()
        }
    }

    impl ops::Neg for &Felt {
        type Output = Felt;

        fn neg(self) -> Self::Output {
            todo!()
        }
    }

    impl iter::Sum for Felt {
        fn sum<I: Iterator<Item = Self>>(_iter: I) -> Self {
            todo!()
        }
    }

    impl<'a> iter::Sum<&'a Felt> for Felt {
        fn sum<I: Iterator<Item = &'a Felt>>(_iter: I) -> Self {
            todo!()
        }
    }
}

#[cfg(feature = "serde")]
mod serde {
    use ::serde::{Deserialize, Serialize};

    use super::*;

    impl Serialize for Felt {
        fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
        where
            S: ::serde::Serializer,
        {
            todo!()
        }
    }

    impl<'de> Deserialize<'de> for Felt {
        fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
        where
            D: ::serde::Deserializer<'de>,
        {
            todo!()
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
        fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
            todo!()
        }
    }

    /// Represents [Felt] in uppercase hexadecimal format.
    impl fmt::UpperHex for Felt {
        fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
            todo!()
        }
    }
}

mod errors {
    use core::fmt;

    use super::*;

    #[cfg(feature = "std")]
    impl std::error::Error for FeltIsZeroError {}

    impl fmt::Display for FeltIsZeroError {
        fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
            todo!()
        }
    }

    #[cfg(feature = "std")]
    impl std::error::Error for FromStrError {}

    impl fmt::Display for FromStrError {
        fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
            todo!()
        }
    }

    #[cfg(feature = "std")]
    impl std::error::Error for FromBytesError {}

    impl fmt::Display for FromBytesError {
        fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
            todo!()
        }
    }
}
