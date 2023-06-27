#![cfg_attr(not(feature = "std"), no_std)]

use core::ops::Mul;

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
};

/// Definition of the Field Element type.
// TODO: See if we can move PartialOrd & Ord to lambdaworks crate
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Felt(FieldElement<Stark252PrimeField>);

impl PartialOrd for Felt {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Felt {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.representative().cmp(&other.0.representative())
    }
}

/// A non-zero [Felt].
pub struct NonZeroFelt(FieldElement<Stark252PrimeField>);

#[derive(Debug)]
pub struct FeltIsZeroError;

#[derive(Debug)]
pub struct FromStrError;

#[derive(Debug)]
pub struct FromBytesError;

impl Felt {
    // TODO: check if its ok to use lazy_static here
    // /// [Felt] constant that's equal to 0.
    // pub const ZERO: Self = Self(FieldElement::<Stark252PrimeField>::zero());

    // /// [Felt] constant that's equal to 1.
    // pub const ONE: Self = Self(FieldElement::<Stark252PrimeField>::one());

    // /// [Felt] constant that's equal to 2.
    // pub const TWO: Self = Self(FieldElement::<Stark252PrimeField>::from(2));

    // /// [Felt] constant that's equal to 3.
    // pub const THREE: Self = Self(FieldElement::<Stark252PrimeField>::from(3));

    // /// Maximum value of [Felt]. Equals to 2^251 + 17 * 2^192.
    // pub const MAX: Self = Self(FieldElement::<Stark252PrimeField>::zero() - FieldElement::<Stark252PrimeField>::one());

    // TODO: const was removed from all methods, check if this is ok/ if we can make these const in lambdaworks
    /// Creates a new [Felt] from its big-endian representation in a [u8] slice.
    pub fn from_bytes_be(bytes: &[u8]) -> Result<Self, FromBytesError> {
        FieldElement::from_bytes_be(bytes)
            .map(|x| Self(x))
            .map_err(|_| FromBytesError)
    }

    /// Creates a new [Felt] from its little-endian representation in a [u8] slice.
    pub fn from_bytes_le(bytes: &[u8]) -> Result<Self, FromBytesError> {
        FieldElement::from_bytes_le(bytes)
            .map(|x| Self(x))
            .map_err(|_| FromBytesError)
    }

    /// Converts to big-endian byte representation in a [u8] array.
    pub fn to_bytes_be(&self) -> [u8; 32] {
        // TODO: implement a no-std version in lambdaworks crate (like to_bytes_le)
        //self.0.to_bytes_be()
        todo!()
    }

    /// Converts to little-endian byte representation in a [u8] array.
    pub fn to_bytes_le(&self) -> [u8; 32] {
        self.0.to_bytes_le()
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
    pub fn is_zero(&self) -> bool {
        self.0 == FieldElement::from_raw(&Stark252PrimeField::ZERO)
    }

    // Question: What is the difference between field_div & floor_div?
    /// Finite field division.
    pub fn field_div(&self, rhs: &NonZeroFelt) -> Self {
        Self(&self.0 / &rhs.0)
    }

    /// Floor division.
    pub fn floor_div(&self, rhs: &NonZeroFelt) -> Self {
        Self(&self.0 / &rhs.0)
    }

    /// Multiplicative inverse.
    pub fn inverse(&self) -> Option<Self> {
        Some(Self(self.0.inv()))
    }

    /// Finds the square root. There may be 2 roots for each square, and the lower one is returned.
    pub fn sqrt(&self) -> Option<Self> {
        let (root_1, root_2) = self.0.sqrt()?;
        let value = FieldElement::new(root_1.representative().min(root_2.representative()));
        Some(Self(value))
    }

    /// Raises `self` to the power of 2.
    pub fn square(&self) -> Self {
        Self(self.0.square())
    }

    /// Raises `self` to the power of `exponent`.
    pub fn pow(&self, exponent: u128) -> Self {
        Self(self.0.pow(exponent))
    }

    // Question: Is mul_mod necessary in this crate?
    // Isn't multiplication mod CAIRO_PRIME more useful?
    // Possible bug: If one wanted to do multiplication modulo CAIRO_PRIME this method would be useless as Felt(CAIRO_PRIME) = 0
    // CHANGE: removed p argument from mul_mod -> doing modulo cairo prime is more useful for the crate
    // Suggestion: leave only mul for multiplication operation within the field and then discuss if mul_mod a different prime is needed and if implementing mod would't be a better solution in that case
    /// Modular multiplication.
    pub fn mul_mod(&self, rhs: &Self) -> Self {
        Self(self.0.mul(rhs.0))
    }

    // Question: Why is this method needed?
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
        &self
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
        &self
    }
}

impl TryFrom<Felt> for NonZeroFelt {
    type Error = FeltIsZeroError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        if value.is_zero() {
            Ok(Self(value.0))
        } else {
            Err(FeltIsZeroError)
        }
    }
}

impl TryFrom<&Felt> for NonZeroFelt {
    type Error = FeltIsZeroError;

    fn try_from(value: &Felt) -> Result<Self, Self::Error> {
        if value.is_zero() {
            Ok(Self(value.0))
        } else {
            Err(FeltIsZeroError)
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
