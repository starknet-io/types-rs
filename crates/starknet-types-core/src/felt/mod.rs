#[cfg(test)]
mod felt_arbitrary;

use core::ops::{Add, Mul, Neg};

use bitvec::array::BitArray;
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};
#[cfg(any(feature = "prime-bigint", test))]
use {lazy_static::lazy_static, num_traits::Num};

#[cfg(feature = "num-traits")]
mod num_traits_impl;
#[cfg(feature = "papyrus-serialization")]
mod papyrus_serialization;

#[cfg(any(feature = "prime-bigint", test))]
lazy_static! {
    pub static ref CAIRO_PRIME_BIGINT: BigInt = BigInt::from_str_radix(
        "800000000000011000000000000000000000000000000000000000000000001",
        16
    )
    .unwrap();
}

#[cfg(target_pointer_width = "64")]
pub type BitArrayStore = [u64; 4];

#[cfg(not(target_pointer_width = "64"))]
pub type BitArrayStore = [u32; 8];

#[cfg(any(test, feature = "alloc"))]
pub extern crate alloc;

use lambdaworks_math::{
    field::{
        element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
    },
    traits::ByteConversion,
    unsigned_integer::element::UnsignedInteger,
};

#[cfg(feature = "arbitrary")]
use arbitrary::{self, Arbitrary, Unstructured};

#[repr(transparent)]
/// Definition of the Field Element type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Felt(pub(crate) FieldElement<Stark252PrimeField>);

/// A non-zero [Felt].
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct NonZeroFelt(FieldElement<Stark252PrimeField>);

impl NonZeroFelt {
    /// Create a [NonZeroFelt] as a constant.
    /// # Safety
    /// If the value is zero will panic.
    pub const fn from_raw(value: [u64; 4]) -> Self {
        assert!(
            value[0] != 0 || value[1] != 0 || value[2] != 0 || value[3] != 0,
            "Felt is zero"
        );
        let value = Felt::from_raw(value);
        Self(value.0)
    }

    /// [Felt] constant that's equal to 1.
    pub const ONE: Self = Self::from_felt_unchecked(Felt(
        FieldElement::<Stark252PrimeField>::from_hex_unchecked("1"),
    ));

    /// [Felt] constant that's equal to 2.
    pub const TWO: Self = Self::from_felt_unchecked(Felt(
        FieldElement::<Stark252PrimeField>::from_hex_unchecked("2"),
    ));

    /// [Felt] constant that's equal to 3.
    pub const THREE: Self = Self::from_felt_unchecked(Felt(
        FieldElement::<Stark252PrimeField>::from_hex_unchecked("3"),
    ));

    /// Maximum value of [Felt]. Equals to 2^251 + 17 * 2^192.
    pub const MAX: Self =
        Self::from_felt_unchecked(Felt(FieldElement::<Stark252PrimeField>::const_from_raw(
            UnsignedInteger::from_limbs([544, 0, 0, 32]),
        )));

    /// Create a [NonZeroFelt] without checking it. If the [Felt] is indeed [Felt::ZERO]
    /// this can lead to undefined behaviour and big security issue.
    /// You should always use the [TryFrom] implementation
    pub const fn from_felt_unchecked(value: Felt) -> Self {
        Self(value.0)
    }
}

#[derive(Debug)]
pub struct FeltIsZeroError;

#[derive(Debug)]
pub struct FromStrError;

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
    /// See [UnisgnedInteger] to understand how it works under the hood.
    pub const fn from_raw(val: [u64; 4]) -> Self {
        Self(FieldElement::<Stark252PrimeField>::const_from_raw(
            UnsignedInteger::from_limbs(val),
        ))
    }

    pub const fn from_hex_unchecked(val: &str) -> Self {
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
        const BASE: Felt = Self(FieldElement::<Stark252PrimeField>::const_from_raw(
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
        const BASE: Felt = Self(FieldElement::<Stark252PrimeField>::const_from_raw(
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

    /// Converts to big-endian bit representation.
    /// This is as performant as [to_bits_le](Felt::to_bits_le)
    #[cfg(target_pointer_width = "64")]
    pub fn to_bits_be(&self) -> BitArray<BitArrayStore> {
        let mut limbs = self.0.representative().limbs;
        limbs.reverse();

        BitArray::new(limbs)
    }

    /// Converts to big-endian bit representation.
    /// This is as performant as [to_bits_le](Felt::to_bits_le)
    #[cfg(all(feature = "alloc", not(target_pointer_width = "64")))]
    pub fn to_bits_be(&self) -> BitArray<BitArrayStore> {
        let mut limbs = self.0.representative().limbs;
        limbs.reverse();

        // Split limbs to adjust to BitArrayStore = [u32; 8]
        let limbs: [u32; 8] = limbs
            .into_iter()
            .flat_map(|n| [(n >> 32) as u32, n as u32])
            .collect::<alloc::vec::Vec<u32>>()
            .try_into()
            .unwrap();

        BitArray::new(limbs)
    }

    /// Helper to produce a hexadecimal formatted string.
    /// Equivalent to calling `format!("{self:#x}")`.
    #[cfg(feature = "alloc")]
    pub fn to_hex_string(&self) -> alloc::string::String {
        alloc::format!("{self:#x}")
    }

    /// Helper to produce a hexadecimal formatted string of 66 chars.
    #[cfg(feature = "alloc")]
    pub fn to_fixed_hex_string(&self) -> alloc::string::String {
        let hex_str = alloc::format!("{self:#x}");
        if hex_str.len() < 66 {
            alloc::format!("0x{:0>64}", hex_str.strip_prefix("0x").unwrap())
        } else {
            hex_str
        }
    }

    /// Converts to little-endian bit representation.
    /// This is as performant as [to_bits_be](Felt::to_bits_be)
    #[cfg(target_pointer_width = "64")]
    pub fn to_bits_le(&self) -> BitArray<BitArrayStore> {
        let limbs = self.0.representative().limbs;

        BitArray::new(limbs)
    }

    /// Converts to little-endian bit representation.
    /// This is as performant as [to_bits_be](Felt::to_bits_be)
    #[cfg(all(feature = "alloc", not(target_pointer_width = "64")))]
    pub fn to_bits_le(&self) -> BitArray<BitArrayStore> {
        let limbs = self.0.representative().limbs;

        // Split limbs to adjust to BitArrayStore = [u32; 8]
        let limbs: [u32; 8] = limbs
            .into_iter()
            .flat_map(|n| [n as u32, (n >> 32) as u32])
            .collect::<alloc::vec::Vec<u32>>()
            .try_into()
            .unwrap();

        BitArray::new(limbs)
    }

    /// Finite field division.
    pub fn field_div(&self, rhs: &NonZeroFelt) -> Self {
        Self(self.0 / rhs.0)
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

    // Implemention taken from Jonathan Lei's starknet-rs
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

    // Implemention taken from Jonathan Lei's starknet-rs
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
            .map_err(|_| FromStrError)
    }

    /// Parse a decimal-encoded number into `Felt`.
    pub fn from_dec_str(dec_string: &str) -> Result<Self, FromStrError> {
        if dec_string.starts_with('-') {
            UnsignedInteger::from_dec_str(dec_string.strip_prefix('-').unwrap())
                .map(|x| Self(FieldElement::from(&x)).neg())
                .map_err(|_| FromStrError)
        } else {
            UnsignedInteger::from_dec_str(dec_string)
                .map(|x| Self(FieldElement::from(&x)))
                .map_err(|_| FromStrError)
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

    #[cfg(feature = "prime-bigint")]
    pub fn prime() -> BigUint {
        (*CAIRO_PRIME_BIGINT).to_biguint().unwrap()
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> Arbitrary<'a> for Felt {
    // Creates an arbitrary `Felt` from unstructured input for fuzzing.
    // It uses the default implementation to create the internal limbs and then
    // uses the usual constructors from `lambdaworks-math`.
    fn arbitrary(u: &mut Unstructured) -> arbitrary::Result<Self> {
        let limbs = <[u64; 4]>::arbitrary(u)?;
        let uint = UnsignedInteger::from_limbs(limbs);
        let felt = FieldElement::new(uint);
        Ok(Felt(felt))
    }
}

/// Allows transparent binary serialization of Felts with `parity_scale_codec`.
#[cfg(feature = "parity-scale-codec")]
impl parity_scale_codec::Encode for Felt {
    fn encode_to<T: parity_scale_codec::Output + ?Sized>(&self, dest: &mut T) {
        dest.write(&self.to_bytes_be());
    }
}

/// Allows transparent binary deserialization of Felts with `parity_scale_codec`
#[cfg(feature = "parity-scale-codec")]
impl parity_scale_codec::Decode for Felt {
    fn decode<I: parity_scale_codec::Input>(
        input: &mut I,
    ) -> Result<Self, parity_scale_codec::Error> {
        let mut buf: [u8; 32] = [0; 32];
        input.read(&mut buf)?;
        Ok(Felt::from_bytes_be(&buf))
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
        if value == Felt::ZERO {
            Err(FeltIsZeroError)
        } else {
            Ok(Self(value.0))
        }
    }
}

impl TryFrom<&Felt> for NonZeroFelt {
    type Error = FeltIsZeroError;

    fn try_from(value: &Felt) -> Result<Self, Self::Error> {
        if *value == Felt::ZERO {
            Err(FeltIsZeroError)
        } else {
            Ok(Self(value.0))
        }
    }
}

impl From<u128> for Felt {
    fn from(value: u128) -> Felt {
        Self(FieldElement::from(&UnsignedInteger::from(value)))
    }
}

impl From<i128> for Felt {
    fn from(value: i128) -> Felt {
        let mut res = Self(FieldElement::from(&UnsignedInteger::from(
            value.unsigned_abs(),
        )));
        if value.is_negative() {
            res = -res;
        }
        res
    }
}

impl From<bool> for Felt {
    fn from(value: bool) -> Felt {
        match value {
            true => Felt::ONE,
            false => Felt::ZERO,
        }
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
        let (sign, bytes) = bigint.to_bytes_le();
        let felt = Felt::from_bytes_le_slice(&bytes);
        if sign == Sign::Minus {
            felt.neg()
        } else {
            felt
        }
    }
}
impl From<&BigUint> for Felt {
    fn from(biguint: &BigUint) -> Felt {
        Felt::from_bytes_le_slice(&biguint.to_bytes_le())
    }
}

impl From<BigUint> for Felt {
    fn from(biguint: BigUint) -> Felt {
        Felt::from_bytes_le_slice(&biguint.to_bytes_le())
    }
}

macro_rules! impl_from {
    ($from:ty, $with:ty) => {
        impl From<$from> for Felt {
            fn from(value: $from) -> Self {
                (value as $with).into()
            }
        }
    };
}

impl_from!(u8, u128);
impl_from!(u16, u128);
impl_from!(u32, u128);
impl_from!(u64, u128);
impl_from!(usize, u128);
impl_from!(i8, i128);
impl_from!(i16, i128);
impl_from!(i32, i128);
impl_from!(i64, i128);
impl_from!(isize, i128);

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

#[cfg(feature = "serde")]
mod serde_impl {
    use alloc::{format, string::String};
    use core::fmt;
    use serde::{de, ser::SerializeSeq, Deserialize, Serialize};

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

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
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
            if *self == Felt::ZERO {
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
    #[cfg(feature = "alloc")]
    impl fmt::UpperHex for Felt {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "0x{}",
                alloc::string::ToString::to_string(&self.0)
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
}

#[cfg(test)]
mod test {
    use super::alloc::{format, string::String, vec::Vec};
    use super::felt_arbitrary::nonzero_felt;
    use super::*;
    use core::ops::Shl;
    use proptest::prelude::*;
    use regex::Regex;
    #[cfg(feature = "serde")]
    use serde_test::{assert_de_tokens, assert_ser_tokens, Configure, Token};

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
            let y = &Felt::from_bytes_be(&res);
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
            let y = &Felt::from_bytes_le(&bytes);
            prop_assert_eq!(x, y);
        }

        #[test]
        #[cfg(feature = "alloc")]
        fn to_hex_string_is_same_as_format(ref x in any::<Felt>()) {
            prop_assert_eq!(alloc::format!("{x:#x}"), x.to_hex_string());
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
        fn non_zero_is_not_zero(x in nonzero_felt()) {
            prop_assert!(x != Felt::ZERO)
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
        fn non_zero_felt_new_is_ok_when_not_zero(x in nonzero_felt()) {
            prop_assert!(NonZeroFelt::try_from(x).is_ok());
            prop_assert_eq!(NonZeroFelt::try_from(x).unwrap().0, x.0);
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

    #[cfg(feature = "prime-bigint")]
    #[test]
    fn prime() {
        assert_eq!(Felt::prime(), CAIRO_PRIME_BIGINT.to_biguint().unwrap());
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
    fn felt_from_hex_unchecked() {
        assert_eq!(Felt::from_hex_unchecked("0"), Felt::from(0));
        assert_eq!(Felt::from_hex_unchecked("1"), Felt::from(1));
        assert_eq!(Felt::from_hex_unchecked("0x2"), Felt::from(2));
        assert_eq!(Felt::from_hex_unchecked("0x0000000003"), Felt::from(3));
        assert_eq!(Felt::from_hex_unchecked("000004"), Felt::from(4));
        assert_eq!(Felt::from_hex_unchecked("0x05b"), Felt::from(91));
        assert_eq!(Felt::from_hex_unchecked("A"), Felt::from(10));
    }
    #[test]
    fn nonzerofelt_from_raw() {
        let one_raw = [
            576460752303422960,
            18446744073709551615,
            18446744073709551615,
            18446744073709551585,
        ];
        assert_eq!(NonZeroFelt::from_raw(one_raw), NonZeroFelt::ONE);
        let two_raw = [
            576460752303422416,
            18446744073709551615,
            18446744073709551615,
            18446744073709551553,
        ];
        assert_eq!(NonZeroFelt::from_raw(two_raw), NonZeroFelt::TWO);
        let nineteen_raw = [
            576460752303413168,
            18446744073709551615,
            18446744073709551615,
            18446744073709551009,
        ];
        assert_eq!(
            NonZeroFelt::from_raw(nineteen_raw),
            NonZeroFelt::try_from(Felt::from(19)).unwrap()
        );
    }

    #[test]
    fn nonzerofelt_from_felt_unchecked() {
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unchecked("9028392")),
            NonZeroFelt::try_from(Felt::from(0x9028392)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unchecked("1")),
            NonZeroFelt::try_from(Felt::from(1)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unchecked("0x2")),
            NonZeroFelt::try_from(Felt::from(2)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unchecked("0x0000000003")),
            NonZeroFelt::try_from(Felt::from(3)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unchecked("000004")),
            NonZeroFelt::try_from(Felt::from(4)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unchecked("0x05b")),
            NonZeroFelt::try_from(Felt::from(91)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unchecked("A")),
            NonZeroFelt::try_from(Felt::from(10)).unwrap()
        );
    }

    #[test]
    #[should_panic(expected = "Felt is zero")]
    fn nonzerofelt_is_zero_from_raw() {
        NonZeroFelt::from_raw([0; 4]);
    }

    #[test]
    fn non_zero_felt_from_zero_should_fail() {
        assert!(NonZeroFelt::try_from(Felt::ZERO).is_err());
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
    #[cfg(feature = "serde")]
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
    #[cfg(feature = "serde")]
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
    fn bigints_to_felt() {
        let one = &*CAIRO_PRIME_BIGINT + BigInt::from(1_u32);
        assert_eq!(Felt::from(&one.to_biguint().unwrap()), Felt::from(1));
        assert_eq!(Felt::from(&one), Felt::from(1));

        let zero = &*CAIRO_PRIME_BIGINT * 99_u32;
        assert_eq!(Felt::from(&zero.to_biguint().unwrap()), Felt::from(0));
        assert_eq!(Felt::from(&zero), Felt::from(0));

        assert_eq!(
            Felt::from(&BigInt::from(-1)),
            Felt::from_hex("0x800000000000011000000000000000000000000000000000000000000000000")
                .unwrap()
        );

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
                Felt::from(&BigInt::from_str_radix(&number_str[2..], 16).unwrap()),
                Felt::from_hex(number_str).unwrap()
            );
            assert_eq!(
                Felt::from(&BigUint::from_str_radix(&number_str[2..], 16).unwrap()),
                Felt::from_hex(number_str).unwrap()
            )
        }
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

    /// Tests proper serialization and deserialization of felts using `parity-scale-codec`.
    #[test]
    #[cfg(feature = "parity-scale-codec")]
    fn parity_scale_codec_serialization() {
        use parity_scale_codec::{Decode, Encode};

        // use an endianness-asymetric number to test that byte order is correct in serialization
        let initial_felt = Felt::from_hex("0xabcdef123").unwrap();

        // serialize the felt
        let serialized_felt = initial_felt.encode();

        // deserialize the felt
        let deserialized_felt = Felt::decode(&mut &serialized_felt[..]).unwrap();

        // check that the deserialized felt is the same as the initial one
        assert_eq!(
            initial_felt, deserialized_felt,
            "mismatch between original and deserialized felts"
        );
    }
    #[cfg(feature = "papyrus-serialization")]
    #[test]
    fn hash_serde() {
        fn enc_len(n_nibbles: usize) -> usize {
            match n_nibbles {
                0..=27 => n_nibbles / 2 + 1,
                28..=33 => 17,
                _ => 32,
            }
        }

        // 64 nibbles are invalid.
        for n_nibbles in 0..64 {
            let mut bytes = [0u8; 32];
            // Set all nibbles to 0xf.
            for i in 0..n_nibbles {
                bytes[31 - (i >> 1)] |= 15 << (4 * (i & 1));
            }
            let h = Felt::from_bytes_be(&bytes);
            let mut res = Vec::new();
            assert!(h.serialize(&mut res).is_ok());
            assert_eq!(res.len(), enc_len(n_nibbles));
            let mut reader = &res[..];
            let d = Felt::deserialize(&mut reader).unwrap();
            assert_eq!(Felt::from_bytes_be(&bytes), d);
        }
    }
}
