#[cfg(feature = "alloc")]
pub extern crate alloc;
#[cfg(feature = "alloc")]
mod alloc_impls;
#[cfg(feature = "apollo-serialization")]
mod apollo_serialization;
#[cfg(feature = "arbitrary")]
mod arbitrary;
#[cfg(test)]
mod felt_arbitrary;
mod non_zero;
#[cfg(feature = "num-traits")]
mod num_traits_impl;
#[cfg(feature = "parity-scale-codec")]
mod parity_scale_codec;
#[cfg(feature = "prime-bigint")]
mod prime_bigint;
mod primitive_conversions;
#[cfg(feature = "secret-felt")]
pub mod secret_felt;
#[cfg(feature = "serde")]
mod serde;

use lambdaworks_math::errors::CreationError;
pub use non_zero::{FeltIsZeroError, NonZeroFelt};

#[cfg(feature = "prime-bigint")]
pub use prime_bigint::CAIRO_PRIME_BIGINT;

use core::ops::{Add, Mul, Neg};
use core::str::FromStr;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};
pub use primitive_conversions::PrimitiveFromFeltError;

use lambdaworks_math::{
    field::{
        element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
    },
    traits::ByteConversion,
    unsigned_integer::element::UnsignedInteger,
};

/// Definition of the Field Element type.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Felt(pub(crate) FieldElement<Stark252PrimeField>);

#[derive(Debug)]
pub struct FromStrError(CreationError);

#[cfg(feature = "std")]
impl std::error::Error for FromStrError {}

impl core::fmt::Display for FromStrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "failed to create Felt from string: ")?;
        match self.0 {
            CreationError::InvalidHexString => write!(f, "invalid hex string"),
            CreationError::InvalidDecString => write!(f, "invalid dec string"),
            CreationError::HexStringIsTooBig => write!(f, "hex string too big"),
            CreationError::RepresentativeOutOfRange => write!(f, "representative out of range"),
            CreationError::EmptyString => write!(f, "empty string"),
        }
    }
}

impl Felt {
    /// [Felt] constant that's equal to 0.
    pub const ZERO: Self = Self(FieldElement::<Stark252PrimeField>::from_hex_unchecked("0"));

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

    /// 2 ** 251
    pub const ELEMENT_UPPER_BOUND: Felt = Felt::from_raw([
        576459263475450960,
        18446744073709255680,
        160989183,
        18446743986131435553,
    ]);

    /// Creates a new [Felt] from the raw internal representation.
    /// See [UnsignedInteger] to understand how it works under the hood.
    pub const fn from_raw(val: [u64; 4]) -> Self {
        Self(FieldElement::<Stark252PrimeField>::const_from_raw(
            UnsignedInteger::from_limbs(val),
        ))
    }

    /// Create a new [Felt] from a hex static string.
    ///
    /// This will panic if used on incorrect values, making it unfit for parsing dynamic values.
    /// It should only be used with static strings, ideally in tests or a `const` context.
    pub const fn from_hex_unwrap(val: &'static str) -> Self {
        Self(FieldElement::<Stark252PrimeField>::from_hex_unchecked(val))
    }

    /// Creates a new [Felt] from its big-endian representation in a [u8; 32] array.
    /// This is as performant as [from_bytes_le](Felt::from_bytes_le).
    pub fn from_bytes_be(bytes: &[u8; 32]) -> Self {
        FieldElement::from_bytes_be(bytes)
            .map(Self)
            .expect("from_bytes_be shouldn't fail for these many bytes")
    }

    /// Creates a new [Felt] from its little-endian representation in a [u8; 32] array.
    /// This is as performant as [from_bytes_le](Felt::from_bytes_be).
    pub fn from_bytes_le(bytes: &[u8; 32]) -> Self {
        FieldElement::from_bytes_le(bytes)
            .map(Self)
            .expect("from_bytes_le shouldn't fail for these many bytes")
    }

    /// Creates a new [Felt] from its big-endian representation in a [u8] slice.
    /// This is as performant as [from_bytes_le](Felt::from_bytes_le_slice).
    /// All bytes in the slice are consumed, as if first creating a big integer
    /// from them, but the conversion is performed in constant space on the stack.
    pub fn from_bytes_be_slice(bytes: &[u8]) -> Self {
        // NB: lambdaworks ignores the remaining bytes when len > 32, so we loop
        // multiplying by BASE, effectively decomposing in base 2^256 to build
        // digits with a length of 32 bytes. This is analogous to splitting the
        // number `xyz` as `x * 10^2 + y * 10^1 + z * 10^0`.
        const BASE: Felt = Felt(FieldElement::<Stark252PrimeField>::const_from_raw(
            UnsignedInteger::from_limbs([
                576413109808302096,
                18446744073700081664,
                5151653887,
                18446741271209837569,
            ]),
        ));
        // Sanity check; gets removed in release builds.
        debug_assert_eq!(BASE, Felt::TWO.pow(256u32));

        let mut factor = Self::ONE;
        let mut res = Self::ZERO;
        let chunks = bytes.rchunks_exact(32);
        let remainder = chunks.remainder();

        for chunk in chunks {
            let digit =
                Self::from_bytes_be(&chunk.try_into().expect("conversion to same-sized array"));
            res += digit * factor;
            factor *= BASE;
        }

        if remainder.is_empty() {
            return res;
        }

        let mut remainder = remainder.iter().rev().cloned();
        let buf: [u8; 32] = core::array::from_fn(move |_| remainder.next().unwrap_or_default());
        let digit = Self::from_bytes_le(&buf);
        res += digit * factor;

        res
    }

    /// Creates a new [Felt] from its little-endian representation in a [u8] slice.
    /// This is as performant as [from_bytes_be](Felt::from_bytes_be_slice).
    /// All bytes in the slice are consumed, as if first creating a big integer
    /// from them, but the conversion is performed in constant space on the stack.
    pub fn from_bytes_le_slice(bytes: &[u8]) -> Self {
        // NB: lambdaworks ignores the remaining bytes when len > 32, so we loop
        // multiplying by BASE, effectively decomposing in base 2^256 to build
        // digits with a length of 32 bytes. This is analogous to splitting the
        // number `xyz` as `x * 10^2 + y * 10^1 + z * 10^0`.
        const BASE: Felt = Felt(FieldElement::<Stark252PrimeField>::const_from_raw(
            UnsignedInteger::from_limbs([
                576413109808302096,
                18446744073700081664,
                5151653887,
                18446741271209837569,
            ]),
        ));
        // Sanity check; gets removed in release builds.
        debug_assert_eq!(BASE, Felt::TWO.pow(256u32));

        let mut factor = Self::ONE;
        let mut res = Self::ZERO;
        let chunks = bytes.chunks_exact(32);
        let remainder = chunks.remainder();

        for chunk in chunks {
            let digit =
                Self::from_bytes_le(&chunk.try_into().expect("conversion to same-sized array"));
            res += digit * factor;
            factor *= BASE;
        }

        if remainder.is_empty() {
            return res;
        }

        let mut remainder = remainder.iter().cloned();
        let buf: [u8; 32] = core::array::from_fn(move |_| remainder.next().unwrap_or_default());
        let digit = Self::from_bytes_le(&buf);
        res += digit * factor;

        res
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

    /// Converts to little-endian bit representation.
    pub fn to_bits_le(&self) -> [bool; 256] {
        self.0.to_bits_le()
    }

    /// Converts to big-endian bit representation.
    pub fn to_bits_be(&self) -> [bool; 256] {
        let mut bits = self.0.to_bits_le();
        bits.reverse();
        bits
    }

    /// Finite field division.
    pub fn field_div(&self, rhs: &NonZeroFelt) -> Self {
        Self((self.0 / rhs.0).expect("dividing by a non zero felt will never fail"))
    }

    /// Truncated quotient between `self` and `rhs`.
    pub fn floor_div(&self, rhs: &NonZeroFelt) -> Self {
        Self(FieldElement::from(
            &(self.0.representative().div_rem(&rhs.0.representative())).0,
        ))
    }

    /// Quotient and remainder between `self` and `rhs`.
    pub fn div_rem(&self, rhs: &NonZeroFelt) -> (Self, Self) {
        let (q, r) = self.0.representative().div_rem(&rhs.0.representative());
        (Self(FieldElement::from(&q)), Self(FieldElement::from(&r)))
    }

    /// Multiplicative inverse inside field.
    pub fn inverse(&self) -> Option<Self> {
        self.0.inv().map(Self).ok()
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

    /// Doubles the point `self`
    pub fn double(&self) -> Self {
        Self(self.0.double())
    }

    /// Raises `self` to the power of `exponent`.
    pub fn pow(&self, exponent: impl Into<u128>) -> Self {
        Self(self.0.pow(exponent.into()))
    }

    /// Raises `self` to the power of `exponent`.
    pub fn pow_felt(&self, exponent: &Felt) -> Self {
        Self(self.0.pow(exponent.0.representative()))
    }

    // Implementation taken from Jonathan Lei's starknet-rs
    // https://github.com/xJonathanLEI/starknet-rs/blob/a3a0050f80e90bd40303256a85783f4b5b18258c/starknet-crypto/src/fe_utils.rs#L20
    /// Modular multiplication between `self` and `rhs` in modulo `p`.
    pub fn mul_mod(&self, rhs: &Self, p: &NonZeroFelt) -> Self {
        let multiplicand = BigInt::from_bytes_be(num_bigint::Sign::Plus, &self.to_bytes_be());
        let multiplier = BigInt::from_bytes_be(num_bigint::Sign::Plus, &rhs.to_bytes_be());
        let modulus = BigInt::from_bytes_be(num_bigint::Sign::Plus, &p.0.to_bytes_be());

        let result = multiplicand.mul(multiplier).mod_floor(&modulus);

        let (_, buffer) = result.to_bytes_be();
        let mut result = [0u8; 32];

        result[(32 - buffer.len())..].copy_from_slice(&buffer[..]);

        Felt::from_bytes_be(&result)
    }

    // Implementation taken from Jonathan Lei's starknet-rs
    // https://github.com/xJonathanLEI/starknet-rs/blob/a3a0050f80e90bd40303256a85783f4b5b18258c/starknet-crypto/src/fe_utils.rs#L46
    /// Multiplicative inverse of `self` in modulo `p`.
    pub fn mod_inverse(&self, p: &NonZeroFelt) -> Option<Self> {
        let operand = BigInt::from_bytes_be(num_bigint::Sign::Plus, &self.0.to_bytes_be());
        let modulus = BigInt::from_bytes_be(num_bigint::Sign::Plus, &p.0.to_bytes_be());

        let extended_gcd = operand.extended_gcd(&modulus);
        if extended_gcd.gcd != BigInt::one() {
            return None;
        }
        let result = if extended_gcd.x < BigInt::zero() {
            extended_gcd.x + modulus
        } else {
            extended_gcd.x
        };

        let (_, buffer) = result.to_bytes_be();
        let mut result = [0u8; 32];
        result[(32 - buffer.len())..].copy_from_slice(&buffer[..]);

        Some(Felt::from_bytes_be(&result))
    }

    /// Remainder of dividing `self` by `n` as integers.
    pub fn mod_floor(&self, n: &NonZeroFelt) -> Self {
        self.div_rem(n).1
    }

    /// Parse a hex-encoded number into `Felt`.
    pub fn from_hex(hex_string: &str) -> Result<Self, FromStrError> {
        FieldElement::from_hex(hex_string)
            .map(Self)
            .map_err(FromStrError)
    }

    /// Parse a decimal-encoded number into `Felt`.
    pub fn from_dec_str(dec_string: &str) -> Result<Self, FromStrError> {
        if dec_string.starts_with('-') {
            UnsignedInteger::from_dec_str(dec_string.strip_prefix('-').unwrap())
                .map(|x| Self(FieldElement::from(&x)).neg())
                .map_err(FromStrError)
        } else {
            UnsignedInteger::from_dec_str(dec_string)
                .map(|x| Self(FieldElement::from(&x)))
                .map_err(FromStrError)
        }
    }

    /// Returns the internal representation of a felt and reverses it to match
    /// starknet-rs mont representation
    pub fn to_raw_reversed(&self) -> [u64; 4] {
        let mut res = self.0.to_raw().limbs;
        res.reverse();
        res
    }

    /// Returns the internal representation of a felt
    pub fn to_raw(&self) -> [u64; 4] {
        self.0.to_raw().limbs
    }
    /// Convert `self`'s representative into an array of `u64` digits,
    /// least significant digits first.
    pub fn to_le_digits(&self) -> [u64; 4] {
        let mut limbs = self.0.representative().limbs;
        limbs.reverse();
        limbs
    }

    /// Convert `self`'s representative into an array of `u64` digits,
    /// most significant digits first.
    pub fn to_be_digits(&self) -> [u64; 4] {
        self.0.representative().limbs
    }

    /// Count the minimum number of bits needed to express `self`'s representative.
    pub fn bits(&self) -> usize {
        self.0.representative().bits_le()
    }

    pub fn to_biguint(&self) -> BigUint {
        let big_digits = self
            .to_le_digits()
            .into_iter()
            .flat_map(|limb| [limb as u32, (limb >> 32) as u32])
            .collect();
        BigUint::new(big_digits)
    }

    pub fn to_bigint(&self) -> BigInt {
        self.to_biguint().into()
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

impl From<&BigInt> for Felt {
    fn from(bigint: &BigInt) -> Felt {
        let (sign, bytes) = bigint.to_bytes_le();
        let felt = Felt::from_bytes_le_slice(&bytes);
        if sign == Sign::Minus {
            felt.neg()
        } else {
            felt
        }
    }
}

impl From<BigInt> for Felt {
    fn from(bigint: BigInt) -> Felt {
        Self::from(&bigint)
    }
}

impl From<&BigUint> for Felt {
    fn from(biguint: &BigUint) -> Felt {
        Felt::from_bytes_le_slice(&biguint.to_bytes_le())
    }
}

impl From<BigUint> for Felt {
    fn from(biguint: BigUint) -> Felt {
        Self::from(&biguint)
    }
}

impl FromStr for Felt {
    type Err = FromStrError;

    /// Converts a hex (0x-prefixed) or decimal string to a [Felt].
    /// e.g., '0x123abc' or '1337'.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("0x") {
            Felt::from_hex(s)
        } else {
            Felt::from_dec_str(s)
        }
    }
}

impl Add<&Felt> for u64 {
    type Output = Option<u64>;

    fn add(self, rhs: &Felt) -> Option<u64> {
        const PRIME_DIGITS_BE_HI: [u64; 3] =
            [0x0800000000000011, 0x0000000000000000, 0x0000000000000000];
        const PRIME_MINUS_U64_MAX_DIGITS_BE_HI: [u64; 3] =
            [0x0800000000000010, 0xffffffffffffffff, 0xffffffffffffffff];

        // Match with the 64 bits digits in big-endian order to
        // characterize how the sum will behave.
        match rhs.to_be_digits() {
            // All digits are `0`, so the sum is simply `self`.
            [0, 0, 0, 0] => Some(self),
            // A single digit means this is effectively the sum of two `u64` numbers.
            [0, 0, 0, low] => self.checked_add(low),
            // Now we need to compare the 3 most significant digits.
            // There are two relevant cases from now on, either `rhs` behaves like a
            // substraction of a `u64` or the result of the sum falls out of range.

            // The 3 MSB only match the prime for Felt::max_value(), which is -1
            // in the signed field, so this is equivalent to substracting 1 to `self`.
            [hi @ .., _] if hi == PRIME_DIGITS_BE_HI => self.checked_sub(1),

            // For the remaining values between `[-u64::MAX..0]` (where `{0, -1}` have
            // already been covered) the MSB matches that of `PRIME - u64::MAX`.
            // Because we're in the negative number case, we count down. Because `0`
            // and `-1` correspond to different MSBs, `0` and `1` in the LSB are less
            // than `-u64::MAX`, the smallest value we can add to (read, substract its
            // magnitude from) a `u64` number, meaning we exclude them from the valid
            // case.
            // For the remaining range, we take the absolute value module-2 while
            // correcting by substracting `1` (note we actually substract `2` because
            // the absolute value itself requires substracting `1`.
            [hi @ .., low] if hi == PRIME_MINUS_U64_MAX_DIGITS_BE_HI && low >= 2 => {
                (self).checked_sub(u64::MAX - (low - 2))
            }
            // Any other case will result in an addition that is out of bounds, so
            // the addition fails, returning `None`.
            _ => None,
        }
    }
}

mod arithmetic {
    use core::{
        iter,
        ops::{self, Neg},
    };

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

    /// Field addition. Never overflows/underflows.
    impl ops::Add<u64> for Felt {
        type Output = Felt;

        fn add(self, rhs: u64) -> Self::Output {
            self + Felt::from(rhs)
        }
    }

    /// Field addition. Never overflows/underflows.
    impl ops::Add<u64> for &Felt {
        type Output = Felt;

        fn add(self, rhs: u64) -> Self::Output {
            self + Felt::from(rhs)
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

    /// Field subtraction. Never overflows/underflows.
    #[allow(clippy::suspicious_arithmetic_impl)]
    impl ops::Sub<Felt> for u64 {
        type Output = Option<u64>;
        fn sub(self, rhs: Felt) -> Self::Output {
            self + &rhs.neg()
        }
    }

    /// Field subtraction. Never overflows/underflows.
    #[allow(clippy::suspicious_arithmetic_impl)]
    impl ops::Sub<&Felt> for u64 {
        type Output = Option<u64>;
        fn sub(self, rhs: &Felt) -> Self::Output {
            self + &rhs.neg()
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<u64> for Felt {
        type Output = Felt;
        fn sub(self, rhs: u64) -> Self::Output {
            self - Self::from(rhs)
        }
    }

    /// Field subtraction. Never overflows/underflows.
    impl ops::Sub<u64> for &Felt {
        type Output = Felt;
        fn sub(self, rhs: u64) -> Self::Output {
            self - Felt::from(rhs)
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

mod formatting {
    use core::fmt;

    use super::*;

    /// Represents [Felt] in decimal by default.
    impl fmt::Display for Felt {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.to_biguint())
        }
    }

    impl fmt::Debug for Felt {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }
}

#[cfg(test)]
mod test {
    use super::alloc::{format, string::String, vec::Vec};
    use super::felt_arbitrary::nonzero_felt;
    use super::*;
    use core::ops::Shl;
    use num_traits::Num;
    use proptest::prelude::*;
    use regex::Regex;

    #[test]
    fn test_debug_format() {
        assert_eq!(format!("{:?}", Felt::ONE), "0x1");
        assert_eq!(format!("{:?}", Felt::from(2)), "0x2");
        assert_eq!(format!("{:?}", Felt::from(12345)), "0x3039");
    }

    // Helper function to generate a vector of bits for testing purposes
    fn generate_be_bits(x: &Felt) -> Vec<bool> {
        // Initialize an empty vector to store the expected bits
        let mut bits = Vec::new();

        // Iterate over each limb in the representative of x
        for limb in x.0.representative().limbs {
            // Convert the limb to a sequence of 8 bytes (u8) in big-endian
            let bytes = limb.to_be_bytes();

            // Iterate over each byte
            for byte in &bytes {
                // Iterate over each bit of the byte
                for i in 0..8 {
                    // Extract the i-th bit of the byte
                    let bit = (*byte >> (7 - i)) & 1;

                    // Push the bit into the expected_bits vector
                    bits.push(bit == 1);
                }
            }
        }

        bits
    }

    proptest! {
        #[test]
        fn new_in_range(ref x in any::<[u8; 32]>()) {
            let x_be = Felt::from_bytes_be(x);
            prop_assert!(x_be < Felt::MAX);
            let x_le = Felt::from_bytes_le(x);
            prop_assert!(x_le < Felt::MAX);
        }

        #[test]
        fn to_be_bytes(ref x in any::<Felt>()) {
            let bytes = x.to_bytes_be();
            let y = &Felt::from_bytes_be(&bytes);
            prop_assert_eq!(x, y);
        }

        #[test]
        fn to_le_bytes(ref x in any::<Felt>()) {
            let bytes = x.to_bytes_le();
            let y = &Felt::from_bytes_le(&bytes);
            prop_assert_eq!(x, y);
        }

        #[test]
        fn to_bits_le(ref x in any::<Felt>()) {
            // Generate the little-endian representation of Felt type x
            let bits: Vec<bool> = x.to_bits_le().into_iter().collect();

            // Get the expected bits in big-endian order
            let mut expected_bits = generate_be_bits(x);

            // Reverse the expected_bits to convert from big-endian to little-endian
            expected_bits.reverse();

            // Assert that the generated bits match the expected bits
            prop_assert_eq!(bits, expected_bits);
        }

        #[test]
        fn to_bits_be(ref x in any::<Felt>()) {
            // Generate the big-endian representation of Felt type x
            let bits: Vec<bool> = x.to_bits_be().into_iter().collect();

            // Get the expected bits in big-endian order
            let expected_bits = generate_be_bits(x);

            // Assert that the generated bits match the expected bits
            prop_assert_eq!(bits, expected_bits);
        }

        #[test]
        fn from_bytes_le_slice_works_for_all_lengths(x in 0..1000usize) {
            let bytes: [u8; 1000] = core::array::from_fn(|i| i as u8);
            let expected = bytes.iter()
                .enumerate()
                .map(|(i, x)| Felt::from(*x) * Felt::from(256).pow(i as u64))
                .take(x)
                .sum::<Felt>();
            let x = Felt::from_bytes_le_slice(&bytes[0..x]);
            prop_assert_eq!(x, expected, "x={:x} expected={:x}", x, expected);
        }

        #[test]
        fn from_bytes_be_slice_works_for_all_lengths(x in 0..1000usize) {
            let bytes: [u8; 1000] = core::array::from_fn(|i| i as u8);
            let expected = bytes.iter()
                .rev()
                .enumerate()
                .map(|(i, x)| Felt::from(*x) * Felt::from(256).pow(i as u64))
                .take(x)
                .sum::<Felt>();
            let x = Felt::from_bytes_be_slice(&bytes[1000-x..1000]);
            prop_assert_eq!(x, expected, "x={:x} expected={:x}", x, expected);
        }

        #[test]
        fn from_bytes_le_in_range(ref x in any::<[u8; 32]>()) {
            let x = Felt::from_bytes_le(x);
            prop_assert!(x <= Felt::MAX);
        }

        #[test]
        fn from_bytes_be_in_range(ref x in any::<[u8; 32]>()) {
            let x = Felt::from_bytes_be(x);
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
        fn mod_floor_in_range(x in any::<Felt>(), n in nonzero_felt()) {
            let nzn = NonZeroFelt(n.0);
            let x_mod_n = x.mod_floor(&nzn);
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
        fn double_in_range(x in any::<Felt>()) {
            prop_assert!(x.double() == x + x);
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
        fn multiplying_by_inverse_yields_multiplicative_neutral(x in nonzero_felt()) {
            prop_assert_eq!(x * x.inverse().unwrap(), Felt::ONE )
        }

        #[test]
        fn inverse_mod_of_zero_is_none(p in nonzero_felt()) {
            let nzp = NonZeroFelt(p.0);
            prop_assert!(Felt::ZERO.mod_inverse(&nzp).is_none());
        }

        #[test]
        fn inverse_mod_in_range(x in nonzero_felt(), p in nonzero_felt()) {
            let nzp = NonZeroFelt(p.0);
            let Some(result) = x.mod_inverse(&nzp) else { return Ok(()) };

            prop_assert!(result <= Felt::MAX);
            prop_assert!(result < p);
            prop_assert!(result.mul_mod(&x, &nzp) == Felt::ONE);
        }

        #[test]
        fn mul_mod_in_range(x in any::<Felt>(), y in any::<Felt>(), p in nonzero_felt()) {
            let nzp = NonZeroFelt(p.0);
            prop_assert!(x.mul_mod(&y, &nzp) <= Felt::MAX);
            prop_assert!(x.mul_mod(&y, &nzp) < p);
        }

        #[test]
        fn to_raw_reversed(mut x in any::<[u64; 4]>()) {
            let felt = Felt::from_raw(x);
            x.reverse();
            prop_assert_eq!(felt.to_raw_reversed(), x);
        }

        #[test]
        fn to_raw(x in any::<[u64; 4]>()) {
            let felt = Felt::from_raw(x);
            prop_assert_eq!(felt.to_raw(), x);
        }
        #[test]
        fn felt_from_bigint(mut x in any::<[u8; 32]>()) {
            x[0] = 0;
            let bigint = BigInt::from_bytes_be(Sign::Plus, &x);
            let felt_from_ref: Felt = (&bigint).into();
            let felt: Felt = bigint.into();
            prop_assert_eq!(felt_from_ref, felt);
            prop_assert_eq!(felt_from_ref.to_bytes_be(), x);
            prop_assert_eq!(felt.to_bytes_be(), x);
        }

        #[test]
        fn felt_from_biguint(mut x in any::<[u8; 32]>()) {
            x[0] = 0;
            let biguint = BigUint::from_bytes_be( &x);
            let felt_from_ref: Felt = (&biguint).into();
            let felt: Felt = biguint.into();
            prop_assert_eq!(felt_from_ref, felt);
            prop_assert_eq!(felt_from_ref.to_bytes_be(), x);
            prop_assert_eq!(felt.to_bytes_be(), x);
        }
        #[test]
        fn iter_sum(a in any::<Felt>(), b in any::<Felt>(), c in any::<Felt>()) {
            prop_assert_eq!([a, b, c].iter().sum::<Felt>(), a + b + c);
            prop_assert_eq!([a, b, c].iter().map(Clone::clone).sum::<Felt>(), a + b + c);
        }

        #[test]
        fn felt_to_fixed_hex_string(a in any::<Felt>()) {
            prop_assert_eq!(a.to_fixed_hex_string().len(), 66);
            let re = Regex::new(r"^0x([0-9a-fA-F]{64})$").unwrap();
            prop_assert!(re.is_match(&a.to_fixed_hex_string()));
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
    fn felt_from_raw() {
        let zero_bytes = [0; 4];
        assert_eq!(Felt::from_raw(zero_bytes), Felt::ZERO);
        let one_raw = [
            576460752303422960,
            18446744073709551615,
            18446744073709551615,
            18446744073709551585,
        ];
        assert_eq!(Felt::from_raw(one_raw), Felt::ONE);
        let nineteen_raw = [
            576460752303413168,
            18446744073709551615,
            18446744073709551615,
            18446744073709551009,
        ];
        assert_eq!(Felt::from_raw(nineteen_raw), Felt::from(19));
    }

    #[test]
    fn felt_from_hex_unwrap() {
        assert_eq!(Felt::from_hex_unwrap("0"), Felt::from(0));
        assert_eq!(Felt::from_hex_unwrap("1"), Felt::from(1));
        assert_eq!(Felt::from_hex_unwrap("0x2"), Felt::from(2));
        assert_eq!(Felt::from_hex_unwrap("0x0000000003"), Felt::from(3));
        assert_eq!(Felt::from_hex_unwrap("000004"), Felt::from(4));
        assert_eq!(Felt::from_hex_unwrap("0x05b"), Felt::from(91));
        assert_eq!(Felt::from_hex_unwrap("A"), Felt::from(10));
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
        assert_eq!(Felt::ONE.pow(5u32), Felt::ONE);
        assert_eq!(Felt::ZERO.pow(5u32), Felt::ZERO);
        assert_eq!(Felt::THREE.pow(0u32), Felt::ONE);
        assert_eq!(
            Felt(FieldElement::from(200)).pow(4u32),
            Felt(FieldElement::from(1600000000))
        );
        assert_eq!(Felt::MAX.pow(9u32), Felt::MAX);
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

    #[test]
    fn inverse_and_mul_mod() {
        let nzps: Vec<NonZeroFelt> = [
            Felt::from(5_i32).try_into().unwrap(),
            Felt::from_hex("0x5").unwrap().try_into().unwrap(),
            Felt::from_hex("0x1234").unwrap().try_into().unwrap(),
            Felt::from_hex("0xabcdef123").unwrap().try_into().unwrap(),
            Felt::from_hex("0xffffffffffffff")
                .unwrap()
                .try_into()
                .unwrap(),
            Felt::from_hex("0xfffffffffffffffffffffffffffffff")
                .unwrap()
                .try_into()
                .unwrap(),
            Felt::MAX.try_into().unwrap(),
        ]
        .to_vec();
        let nums = [
            Felt::from_hex("0x0").unwrap(),
            Felt::from_hex("0x1").unwrap(),
            Felt::from_hex("0x2").unwrap(),
            Felt::from_hex("0x5").unwrap(),
            Felt::from_hex("0x123abc").unwrap(),
            Felt::from_hex("0xabcdef9812367312").unwrap(),
            Felt::from_hex("0xffffffffffffffffffffffffffffff").unwrap(),
            Felt::from_hex("0xffffffffffffffffffffffffffffffffffffffffff").unwrap(),
            Felt::MAX,
        ];

        for felt in nums {
            for nzp in nzps.iter() {
                let result = felt.mod_inverse(nzp);
                if result.is_some() {
                    assert_eq!(result.unwrap().mul_mod(&felt, nzp), Felt::ONE);
                }
            }
        }
    }

    #[test]
    fn check_mul_mod() {
        let x = Felt::from_dec_str(
            "3618502788666131213697322783095070105623107215331596699973092056135872020480",
        )
        .unwrap();
        let y = Felt::from_dec_str("46118400291").unwrap();
        let p: NonZeroFelt = Felt::from_dec_str("123987312893120893724347692364")
            .unwrap()
            .try_into()
            .unwrap();
        let expected_result = Felt::from_dec_str("68082278891996790254001523512").unwrap();

        assert_eq!(x.mul_mod(&y, &p), expected_result);
    }

    #[test]
    fn felt_to_bigints() {
        let numbers_str = [
            "0x0",
            "0x1",
            "0x10",
            "0x8000000000000110000000000",
            "0xffffffffffffff",
            "0xffffffffefff12380777abcd",
        ];

        for number_str in numbers_str {
            assert_eq!(
                Felt::from_hex(number_str).unwrap().to_bigint(),
                BigInt::from_str_radix(&number_str[2..], 16).unwrap()
            );

            assert_eq!(
                Felt::from_hex(number_str).unwrap().to_biguint(),
                BigUint::from_str_radix(&number_str[2..], 16).unwrap()
            );
        }
    }

    #[test]
    fn bool_into_felt() {
        let zero: Felt = false.into();
        let one: Felt = true.into();
        assert_eq!(one, Felt::ONE);
        assert_eq!(zero, Felt::ZERO);
    }

    #[test]
    fn felt_from_hex_upper_bound_limit() {
        assert!(
            Felt::from_hex("0x800000000000011000000000000000000000000000000000000000000000001")
                .is_ok()
        );
        assert!(
            Felt::from_hex("0x800000000000011000000000000000000000000000000000000000000000002")
                .is_err()
        );
        assert!(Felt::from_hex(&format!("0x{}", "f".repeat(63))).is_err());
    }
}
