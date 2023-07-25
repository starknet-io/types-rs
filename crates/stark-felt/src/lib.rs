#![cfg_attr(not(feature = "std"), no_std)]

use bitvec::array::BitArray;

#[cfg(test)]
mod arbitrary;

#[cfg(target_pointer_width = "64")]
pub type BitArrayStore = [u64; 4];

#[cfg(not(target_pointer_width = "64"))]
pub type BitArrayStore = [u32; 8];

#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::string::ToString;
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

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
    /// This is as performant as [from_bytes_le](Felt::from_bytes_le)
    pub fn from_bytes_be(bytes: &[u8]) -> Result<Self, FromBytesError> {
        FieldElement::from_bytes_be(bytes)
            .map(Self)
            .map_err(|_| FromBytesError)
    }

    /// Creates a new [Felt] from its little-endian representation in a [u8] slice.
    /// This is as performant as [from_bytes_be](Felt::from_bytes_be)
    pub fn from_bytes_le(bytes: &[u8]) -> Result<Self, FromBytesError> {
        FieldElement::from_bytes_le(bytes)
            .map(Self)
            .map_err(|_| FromBytesError)
    }

    /// Converts to big-endian byte representation in a [u8] array.
    /// This is as performant as [to_bytes_le](Felt::to_bytes_le)
    pub fn to_bytes_be(&self) -> [u8; 32] {
        self.0.to_bytes_be()
    }

    /// Converts to little-endian byte representation in a [u8] array.
    /// This is as performant as [to_bytes_be](Felt::to_bytes_be)
    pub fn to_bytes_le(&self) -> [u8; 32] {
        self.0.to_bytes_le()
    }

    /// Converts to big-endian bit representation.
    /// This is as performant as [to_bits_le](Felt::to_bits_le)
    pub fn to_bits_be(&self) -> BitArray<BitArrayStore> {
        let mut limbs = self.0.representative().limbs;
        limbs.reverse();

        #[cfg(not(target_pointer_width = "64"))]
        // Split limbs to adjust to BitArrayStore = [u32; 8]
        let limbs: [u32; 8] = limbs
            .into_iter()
            .flat_map(|n| [(n >> 32) as u32, n as u32])
            .collect::<Vec<u32>>()
            .try_into()
            .unwrap();

        BitArray::new(limbs)
    }

    /// Converts to little-endian bit representation.
    /// This is as performant as [to_bits_be](Felt::to_bits_be)
    pub fn to_bits_le(&self) -> BitArray<BitArrayStore> {
        let limbs = self.0.representative().limbs;

        #[cfg(not(target_pointer_width = "64"))]
        // Split limbs to adjust to BitArrayStore = [u32; 8]
        let limbs: [u32; 8] = limbs
            .into_iter()
            .flat_map(|n| [n as u32, (n >> 32) as u32])
            .collect::<Vec<u32>>()
            .try_into()
            .unwrap();

        BitArray::new(limbs)
    }

    /// Checks if `self` is equal to [Felt::Zero].
    pub fn is_zero(&self) -> bool {
        *self == Felt::ZERO
    }
    /// Finite field division.
    pub fn field_div(&self, rhs: &NonZeroFelt) -> Self {
        Self(self.0 / rhs.0)
    }

    /// Floor division.
    pub fn floor_div(&self, rhs: &NonZeroFelt) -> Self {
        Self(FieldElement::from(
            &(self.0.representative().div_rem(&rhs.0.representative())).0,
        ))
    }

    /// Multiplicative inverse.
    pub fn inverse(&self) -> Option<Self> {
        Some(Self(self.0.inv()))
    }

    /// Finds the square root. There may be 2 roots for each square, and the lower one is returned.
    pub fn sqrt(&self) -> Option<Self> {
        let (root_1, root_2) = self.0.sqrt()?;
        Some(Self(core::cmp::min(root_1, root_2)))
    }

    /// Raises `self` to the power of 2.
    pub fn square(&self) -> Self {
        Self(self.0.square())
    }

    /// Raises `self` to the power of `exponent`.
    pub fn pow(&self, exponent: u128) -> Self {
        Self(self.0.pow(exponent))
    }

    /// Performs self modulo n, with n being smaller that the stark field prime.
    pub fn mod_floor(&self, n: &Self) -> Self {
        Self(FieldElement::from(
            &(self.0).representative().div_rem(&n.0.representative()).1,
        ))
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
            let mut base = Self::ZERO;
            iter.for_each(|addend| base += addend);
            base
        }
    }

    impl<'a> iter::Sum<&'a Felt> for Felt {
        fn sum<I: Iterator<Item = &'a Felt>>(iter: I) -> Self {
            let mut base = Self::ZERO;
            iter.for_each(|addend| base += addend);
            base
        }
    }
}

#[cfg(feature = "serde")]
mod serde {
    use core::fmt;

    use ::serde::{de, ser::SerializeSeq, Deserialize, Serialize};

    use super::*;

    impl Serialize for Felt {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: ::serde::Serializer,
        {
            if serializer.is_human_readable() {
                serializer.serialize_str(&format!("{:x}", self))
            } else {
                let mut seq = serializer.serialize_seq(Some(32))?;
                for b in self.to_bytes_be() {
                    seq.serialize_element(&b)?;
                }
                seq.end()
            }
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
            value
                .strip_prefix("0x")
                .and_then(|v| FieldElement::<Stark252PrimeField>::from_hex(v).ok())
                .map(Felt)
                .ok_or(String::from("Expected hex string to be prefixed by '0x'"))
                .map_err(de::Error::custom)
        }
    }
}

mod formatting {
    use core::fmt;

    use super::*;

    /// Represents [Felt] in decimal by default.
    impl fmt::Display for Felt {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if self.is_zero() {
                return write!(f, "0");
            }

            let mut buf = [0u8; 4 * 20];
            let mut i = buf.len() - 1;
            let mut current = self.0.representative();
            let ten = UnsignedInteger::from(10_u16);

            loop {
                let (quotient, remainder) = current.div_rem(&ten);
                let digit = remainder.limbs[3] as u8;
                buf[i] = digit + b'0';
                current = quotient;
                if current == UnsignedInteger::from(0_u16) {
                    break;
                }
                i -= 1;
            }

            // sequence of `'0'..'9'` chars is guaranteed to be a valid UTF8 string
            let s = core::str::from_utf8(&buf[i..]).unwrap();
            fmt::Display::fmt(s, f)
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
            write!(
                f,
                "0x{}",
                self.0
                    .to_string()
                    .strip_prefix("0x")
                    .unwrap()
                    .to_uppercase()
            )
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
    use core::ops::Shl;

    use crate::arbitrary::nonzero_felt;

    use super::*;

    use proptest::prelude::*;
    use serde_test::{assert_de_tokens, assert_ser_tokens, Configure, Token};

    proptest! {
        #[test]
        fn new_in_range(ref x in any::<[u8; 40]>()) {
            let x_be = Felt::from_bytes_be(x).unwrap();
            prop_assert!(x_be < Felt::MAX);
            let x_le = Felt::from_bytes_le(x).unwrap();
            prop_assert!(x_le < Felt::MAX);
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
        fn from_bytes_be_in_range(ref x in any::<[u8; 40]>()) {
            let x = Felt::from_bytes_be(x).unwrap();
            prop_assert!(x <= Felt::MAX);
        }

        #[test]
        fn neg_in_range(x in any::<Felt>()) {
            prop_assert!(-x <= Felt::MAX);
        }

        #[test]
        fn sub(ref x in any::<Felt>(), ref y in any::<Felt>()) {
            // x - y
            prop_assert!(x - y <= Felt::MAX);
            prop_assert_eq!(Felt::MAX + x - y + Felt::ONE, x - y);
            // y - x
            prop_assert!(y - x <= Felt::MAX);
            prop_assert_eq!(Felt::MAX + y - x + Felt::ONE, y - x);
        }

        #[test]
        fn sub_assign_in_range(mut x in any::<Felt>(), y in any::<Felt>()) {
            x -= y;
            prop_assert!(x <= Felt::MAX);
            // test reference variant
            x -= &y;
            prop_assert!(x <= Felt::MAX);
        }

        #[test]
        fn mul(ref x in any::<Felt>(), ref y in any::<Felt>()) {
            prop_assert_eq!(x * y, y * x);
            prop_assert!(x * y <= Felt::MAX);
        }

        #[test]
        fn mul_assign_in_range(mut x in any::<Felt>(), y in any::<Felt>()) {
            x *= y;
            prop_assert!(x <= Felt::MAX);
            // test reference variant
            x *= &y;
            prop_assert!(x <= Felt::MAX);
        }

        #[test]
        fn mod_floor_in_range(x in any::<Felt>(), n in any::<Felt>()) {
            let x_mod_n = x.mod_floor(&n);
            prop_assert!(x_mod_n <= Felt::MAX);
            prop_assert!(x_mod_n < n);
        }

        #[test]
        fn field_div_is_mul_inv(x in any::<Felt>(), y in nonzero_felt()) {
            let q = x.field_div(&NonZeroFelt(y.0));
            prop_assert!(q <= Felt::MAX);
            prop_assert_eq!(q * y, x);
        }

        #[test]
        fn floor_div_is_mul_inv(x in any::<Felt>(), y in nonzero_felt()) {
            let x = Felt(FieldElement::from(&x.0.representative().shl(127)));
            let y = Felt(FieldElement::from(&y.0.representative().shl(127)));
            let q = x.field_div(&NonZeroFelt(y.0));
            prop_assert!(q <= Felt::MAX);
            prop_assert_eq!(q * y, x);
        }

        #[test]
        fn pow_in_range(base in any::<Felt>(), exp in 0..u128::MAX){
            prop_assert!(base.pow(exp) <= Felt::MAX);
        }

        #[test]
        fn add_in_range(x in any::<Felt>(), y in any::<Felt>()){
            prop_assert!(x + y <= Felt::MAX);
        }

        #[test]
        fn zero_additive_identity(x in any::<Felt>()) {
            prop_assert_eq!(x, x + Felt::ZERO);
            prop_assert_eq!(x, Felt::ZERO + x);
        }

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

        #[test]
        fn sqrt_is_inv_square(x in any::<Felt>()) {
            // we use x = x' * x' so x has a square root
            let sqrt = (x * x).sqrt().unwrap();
            prop_assert!( sqrt == x || -sqrt == x)
        }

        #[test]
        fn square_in_range(x in any::<Felt>()) {
            prop_assert!(x.square() <= Felt::MAX);
        }

        #[test]
        fn square_x_is_x_mul_x(x in any::<Felt>()) {
            prop_assert_eq!(x.square(), x * x);
        }

        #[test]
        fn square_is_inv_sqrt(x in any::<Felt>()) {
            let sqrt = x.square().sqrt().unwrap();
            prop_assert!( sqrt == x || -sqrt == x)
        }

        #[test]
        fn non_zero_is_not_zero(x in nonzero_felt()) {
            prop_assert!(!x.is_zero())
        }

        #[test]
        fn multiplying_by_inverse_yields_multiplicative_neutral(x in nonzero_felt()) {
            prop_assert_eq!(x * x.inverse().unwrap(), Felt::ONE )
        }

        #[test]
        fn non_zero_felt_new_is_ok_when_not_zero(x in nonzero_felt()) {
            prop_assert!(NonZeroFelt::try_from(x).is_ok());
            prop_assert_eq!(NonZeroFelt::try_from(x).unwrap().0, x.0);
        }

        #[test]
        fn iter_sum(a in any::<Felt>(), b in any::<Felt>(), c in any::<Felt>()) {
            prop_assert_eq!([a, b, c].iter().sum::<Felt>(), a + b + c);
            prop_assert_eq!([a, b, c].iter().map(Clone::clone).sum::<Felt>(), a + b + c);
        }
    }

    #[test]
    fn constant_zero() {
        let mut zero_bytes = 0_u64.to_le_bytes().to_vec();
        zero_bytes.extend_from_slice(&[0; 24]);
        assert_eq!(Felt::ZERO.to_bytes_le().to_vec(), zero_bytes);
    }

    #[test]
    fn constant_one() {
        let mut one_bytes = 1_u64.to_le_bytes().to_vec();
        one_bytes.extend_from_slice(&[0; 24]);
        assert_eq!(Felt::ONE.to_bytes_le().to_vec(), one_bytes);
    }

    #[test]
    fn constant_two() {
        let mut two_bytes = 2_u64.to_le_bytes().to_vec();
        two_bytes.extend_from_slice(&[0; 24]);
        assert_eq!(Felt::TWO.to_bytes_le().to_vec(), two_bytes);
    }

    #[test]
    fn constant_three() {
        let mut three_bytes = 3_u64.to_le_bytes().to_vec();
        three_bytes.extend_from_slice(&[0; 24]);
        assert_eq!(Felt::THREE.to_bytes_le().to_vec(), three_bytes);
    }

    #[test]
    fn constant_max() {
        let max_bytes = [
            8, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        assert_eq!(Felt::MAX.to_bytes_be(), max_bytes);
    }

    #[test]
    fn zero_is_zero() {
        assert!(Felt::ZERO.is_zero());
    }

    #[test]
    fn non_zero_felt_from_zero_should_fail() {
        assert!(NonZeroFelt::try_from(Felt::ZERO).is_err());
    }

    #[test]
    fn default_is_zero() {
        assert!(Felt::default().is_zero());
    }

    #[test]
    fn mul_operations() {
        assert_eq!(Felt::ONE * Felt::THREE, Felt::THREE);
        assert_eq!(Felt::ZERO * Felt::MAX, Felt::ZERO);
        assert_eq!(
            Felt(FieldElement::from(200)) * Felt::THREE,
            Felt(FieldElement::from(600))
        );
        assert_eq!(Felt::MAX * Felt::TWO, Felt::MAX - Felt::ONE);
    }

    #[test]
    fn add_operations() {
        assert_eq!(Felt::ONE + Felt::TWO, Felt::THREE);
        assert_eq!(Felt::ZERO + Felt::MAX, Felt::MAX);
        assert_eq!(
            Felt(FieldElement::from(200)) + Felt::THREE,
            Felt(FieldElement::from(203))
        );
        assert_eq!(Felt::MAX + Felt::TWO, Felt::ONE);
    }

    #[test]
    fn sub_operations() {
        assert_eq!(Felt::TWO - Felt::ONE, Felt::ONE);
        assert_eq!(Felt::MAX - Felt::ZERO, Felt::MAX);
        assert_eq!(
            Felt(FieldElement::from(200)) - Felt::THREE,
            Felt(FieldElement::from(197))
        );
        assert_eq!(Felt::ZERO - Felt::ONE, Felt::MAX);
    }

    #[test]
    fn pow_operations() {
        assert_eq!(Felt::ONE.pow(5), Felt::ONE);
        assert_eq!(Felt::ZERO.pow(5), Felt::ZERO);
        assert_eq!(Felt::THREE.pow(0), Felt::ONE);
        assert_eq!(
            Felt(FieldElement::from(200)).pow(4),
            Felt(FieldElement::from(1600000000))
        );
        assert_eq!(Felt::MAX.pow(9), Felt::MAX);
    }

    #[test]
    fn deserialize() {
        assert_de_tokens(&Felt::ZERO, &[Token::String("0x0")]);
        assert_de_tokens(&Felt::TWO, &[Token::String("0x2")]);
        assert_de_tokens(&Felt::THREE, &[Token::String("0x3")]);
        assert_de_tokens(
            &Felt::MAX,
            &[Token::String(
                "0x800000000000011000000000000000000000000000000000000000000000000",
            )],
        );
    }

    #[test]
    fn serialize() {
        assert_ser_tokens(&Felt::ZERO.readable(), &[Token::String("0x0")]);
        assert_ser_tokens(&Felt::TWO.readable(), &[Token::String("0x2")]);
        assert_ser_tokens(&Felt::THREE.readable(), &[Token::String("0x3")]);
        assert_ser_tokens(
            &Felt::MAX.readable(),
            &[Token::String(
                "0x800000000000011000000000000000000000000000000000000000000000000",
            )],
        );

        assert_ser_tokens(
            &Felt::ZERO.compact(),
            &[
                Token::Seq { len: Some(32) },
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::SeqEnd,
            ],
        );
        assert_ser_tokens(
            &Felt::TWO.compact(),
            &[
                Token::Seq { len: Some(32) },
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(2),
                Token::SeqEnd,
            ],
        );
        assert_ser_tokens(
            &Felt::THREE.compact(),
            &[
                Token::Seq { len: Some(32) },
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(3),
                Token::SeqEnd,
            ],
        );
        assert_ser_tokens(
            &Felt::MAX.compact(),
            &[
                Token::Seq { len: Some(32) },
                Token::U8(8),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(17),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::U8(0),
                Token::SeqEnd,
            ],
        );
    }

    #[test]
    fn display_lower_hex() {
        assert_eq!(format!("{:#x}", Felt::ZERO), format!("{:#x}", 0_u64));
        assert_eq!(format!("{:#x}", Felt::TWO), format!("{:#x}", 2_u64));
        assert_eq!(format!("{:#x}", Felt::THREE), format!("{:#x}", 3_u64));
        assert_eq!(
            format!("{:#x}", Felt(FieldElement::from(200))),
            format!("{:#x}", 200_u64)
        );
        assert_eq!(
            format!("{:#x}", Felt::MAX),
            String::from("0x800000000000011000000000000000000000000000000000000000000000000")
        );
    }

    #[test]
    fn display_upper_hex() {
        assert_eq!(format!("{:#X}", Felt::ZERO), format!("{:#X}", 0_u64));
        assert_eq!(format!("{:#X}", Felt::TWO), format!("{:#X}", 2_u64));
        assert_eq!(format!("{:#X}", Felt::THREE), format!("{:#X}", 3_u64));
        assert_eq!(
            format!("{:#X}", Felt(FieldElement::from(200))),
            format!("{:#X}", 200_u64)
        );
        assert_eq!(
            format!("{:#X}", Felt::MAX),
            String::from("0x800000000000011000000000000000000000000000000000000000000000000")
        );
    }

    #[test]
    fn display_decimal() {
        assert_eq!(format!("{}", Felt::ZERO), format!("{}", 0_u64));
        assert_eq!(format!("{}", Felt::TWO), format!("{}", 2_u64));
        assert_eq!(format!("{}", Felt::THREE), format!("{}", 3_u64));
        assert_eq!(
            format!("{}", Felt(FieldElement::from(200))),
            format!("{}", 200_u64)
        );
        assert_eq!(
            format!("{}", Felt::MAX),
            String::from(
                "3618502788666131213697322783095070105623107215331596699973092056135872020480"
            )
        );
    }
}
