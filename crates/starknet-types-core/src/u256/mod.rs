//! A Cairo-like u256 type.
//!
//! This `U256` type purpose is not to be used to perform arithmetic operations,
//! but rather to offer a handy interface to convert from and to Cairo's u256 values.
//! Indeed, the Cairo language represent u256 values as a two felts struct,
//! representing the `low` and `high` 128 bits of the value.
//! We mirror this representation, allowing for efficient serialization/deserializatin.
//!
//! We recommend you create From/Into implementation to bridge the gap between your favourite u256 type,
//! and the one provided by this crate.

#[cfg(feature = "num-traits")]
mod num_traits_impl;
mod primitive_conversions;
#[cfg(test)]
mod tests;

use core::{fmt::Debug, str::FromStr};

use crate::felt::{Felt, PrimitiveFromFeltError};

/// Error types that can occur when parsing a string into a U256.
#[derive(Debug)]
pub enum FromStrError {
    /// The string contain too many characters to be the representation of a valid u256 value.
    StringTooLong,
    /// The parsed value exceeds the maximum representable value for U256.
    ValueTooBig,
    /// The string contains invalid characters for the expected format.
    Invalid,
    /// Underlying u128 parsing failed.
    Parse(<u128 as FromStr>::Err),
}

impl core::fmt::Display for FromStrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FromStrError::ValueTooBig => core::fmt::Display::fmt("value too big for u256", f),
            FromStrError::Invalid => core::fmt::Display::fmt("invalid characters", f),
            FromStrError::Parse(e) => {
                // Avoid using format as it requires `alloc`
                core::fmt::Display::fmt("invalid string: ", f)?;
                core::fmt::Display::fmt(e, f)
            }
            FromStrError::StringTooLong => {
                core::fmt::Display::fmt("too many characters to be a valid u256 representation", f)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for FromStrError {}

/// A 256-bit unsigned integer represented as two 128-bit components.
///
/// The internal representation uses big-endian ordering where `high` contains
/// the most significant 128 bits and `low` contains the least significant 128 bits.
/// This reflects the way u256 are represented in the Cairo language.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct U256 {
    high: u128,
    low: u128,
}

impl U256 {
    /// Returns the high 128 bits of the U256 value.
    pub fn high(&self) -> u128 {
        self.high
    }

    /// Returns the low 128 bits of the U256 value.
    pub fn low(&self) -> u128 {
        self.low
    }

    /// Constructs a U256 from explicit high and low 128-bit components.
    ///
    /// This is the most direct way to create a U256 when you already have
    /// the component values separated.
    pub fn from_parts(high: u128, low: u128) -> Self {
        Self { low, high }
    }

    /// Attempts to construct a U256 from two Felt values representing high and low parts.
    ///
    /// This conversion can fail if either Felt value cannot be represented as a u128,
    /// which would indicate the Felt contains a value outside the valid range.
    pub fn try_from_felt_parts(high: Felt, low: Felt) -> Result<Self, PrimitiveFromFeltError> {
        Ok(Self {
            high: high.try_into()?,
            low: low.try_into()?,
        })
    }

    /// Attempts to construct a U256 from decimal string representations of high and low parts.
    ///
    /// Both strings must be valid decimal representations that fit within u128 range.
    pub fn try_from_dec_str_parts(high: &str, low: &str) -> Result<Self, <u128 as FromStr>::Err> {
        Ok(Self {
            high: high.parse()?,
            low: low.parse()?,
        })
    }

    /// Attempts to construct a U256 from hexadecimal string representations of high and low parts.
    ///
    /// Both strings must be valid hexadecimal (prefixed or not) representations that fit within u128 range.
    pub fn try_from_hex_str_parts(high: &str, low: &str) -> Result<Self, <u128 as FromStr>::Err> {
        let high = if high.starts_with("0x") || high.starts_with("0X") {
            &high[2..]
        } else {
            high
        };
        let low = if low.starts_with("0x") || low.starts_with("0X") {
            &low[2..]
        } else {
            low
        };

        Ok(Self {
            high: u128::from_str_radix(high, 16)?,
            low: u128::from_str_radix(low, 16)?,
        })
    }

    /// Parses a hexadecimal string into a U256 value.
    ///
    /// Accepts strings with or without "0x"/"0X" prefixes and handles leading zero removal.
    /// The implementation automatically determines the split between high and low components
    /// based on string length, with values over 32 hex digits requiring high component usage.
    pub fn from_hex_str(hex_str: &str) -> Result<Self, FromStrError> {
        // Remove prefix
        let string_without_prefix = if hex_str.starts_with("0x") || hex_str.starts_with("0X") {
            &hex_str[2..]
        } else {
            hex_str
        };

        if string_without_prefix.is_empty() {
            return Err(FromStrError::Invalid);
        }

        // Remove leading zero
        let string_without_zero_padding = string_without_prefix.trim_start_matches('0');

        let (high, low) = if string_without_zero_padding.is_empty() {
            // The string was uniquely made out of of `0`
            (0, 0)
        } else if string_without_zero_padding.len() > 64 {
            return Err(FromStrError::StringTooLong);
        } else if string_without_zero_padding.len() > 32 {
            // The 32 last characters are the `low` u128 bytes,
            // all the other ones are the `high` u128 bytes.
            let delimiter_index = string_without_zero_padding.len() - 32;
            (
                u128::from_str_radix(&string_without_zero_padding[0..delimiter_index], 16)
                    .map_err(FromStrError::Parse)?,
                u128::from_str_radix(&string_without_zero_padding[delimiter_index..], 16)
                    .map_err(FromStrError::Parse)?,
            )
        } else {
            // There is no `high` bytes.
            (
                0,
                u128::from_str_radix(string_without_zero_padding, 16)
                    .map_err(FromStrError::Parse)?,
            )
        };

        Ok(U256 { high, low })
    }

    /// Parses a decimal string into a `u256`.
    ///
    /// Custom arithmetic is executed in order to efficiently parse the input as two `u128` values.
    ///
    /// This implementation performs digit-by-digit multiplication to handle values
    /// that exceed u128 range. The algorithm uses overflow detection to prevent
    /// silent wraparound and ensures accurate representation of large decimal numbers.
    /// Values with more than 78 decimal digits are rejected as they exceed U256 capacity.
    pub fn from_dec_str(dec_str: &str) -> Result<Self, FromStrError> {
        if dec_str.is_empty() {
            return Err(FromStrError::Invalid);
        }

        // Ignore leading zeros
        let string_without_zero_padding = dec_str.trim_start_matches('0');

        let (high, low) = if string_without_zero_padding.is_empty() {
            // The string was uniquely made out of of `0`
            (0, 0)
        } else if string_without_zero_padding.len() > 78 {
            return Err(FromStrError::StringTooLong);
        } else {
            let mut low = 0u128;
            let mut high = 0u128;

            // b is ascii value of the char less the ascii value of the char '0'
            // which happen to be equal to the number represented by the char.
            // b = ascii(char) - ascii('0')
            for b in string_without_zero_padding
                .bytes()
                .map(|b| b.wrapping_sub(b'0'))
            {
                // Using `wrapping_sub` all non 0-9 characters will yield a value greater than 9.
                if b > 9 {
                    return Err(FromStrError::Invalid);
                }

                // We use a [long multiplication](https://en.wikipedia.org/wiki/Multiplication_algorithm#Long_multiplication)
                // algorithm to perform the computation.
                // The idea is that if
                // `v = (high << 128) + low`
                // then
                // `v * 10 = ((high * 10) << 128) + low * 10`

                // Compute `high * 10`, return error on overflow.
                let (new_high, did_overflow) = high.overflowing_mul(10);
                if did_overflow {
                    return Err(FromStrError::ValueTooBig);
                }
                // Now we want to compute `low * 10`, but in case it overflows, we want to carry rather than error.
                // To do so, we perform another long multiplication to get both the result and carry values,
                // this time breaking the u128 (low) value into two u64 (low_low and low_high),
                // perform multiplication on each part individually, extracting an eventual carry, and finally
                // combining them back.
                //
                // Any overflow on the high part will result in an error.
                // Any overflow on the low part should be handled by carrying the extra amount to the high part.
                let (new_low, carry) = {
                    let low_low = low as u64;
                    let low_high = (low >> 64) as u64;

                    // Both of those values cannot overflow, as they are u64 stored into a u128.
                    // Instead they will just start using the highest half part of their bytes.
                    let low_low = (low_low as u128) * 10;
                    let low_high = (low_high as u128) * 10;

                    // The carry of the multiplication per 10 is in the highest 64 bytes of the `low_high` part.
                    let carry_mul_10 = low_high >> 64;
                    // We shift back the bytes, erasing any carry we may have.
                    let low_high_without_carry = low_high << 64;

                    // By adding back the two low parts together we get its new value.
                    let (new_low, did_overflow) = low_low.overflowing_add(low_high_without_carry);
                    // I couldn't come up with a value where `did_overflow` is true,
                    // but better safe than sorry
                    (new_low, carry_mul_10 + if did_overflow { 1 } else { 0 })
                };

                // Add carry to high if it exists.
                let new_high = if carry != 0 {
                    let (new_high, did_overflow) = new_high.overflowing_add(carry);
                    // Error if it overflows.
                    if did_overflow {
                        return Err(FromStrError::ValueTooBig);
                    }
                    new_high
                } else {
                    new_high
                };

                // Add the new digit to low.
                let (new_low, did_overflow) = new_low.overflowing_add(b.into());

                // Add one to high if the previous operation overflowed.
                if did_overflow {
                    let (new_high, did_overflow) = new_high.overflowing_add(1);
                    // Error if it overflows.
                    if did_overflow {
                        return Err(FromStrError::ValueTooBig);
                    }
                    high = new_high;
                } else {
                    high = new_high;
                }

                low = new_low
            }

            (high, low)
        };

        Ok(U256 { high, low })
    }
}

impl FromStr for U256 {
    type Err = FromStrError;

    /// Parses a string into a U256 by detecting the format automatically.
    ///
    /// Strings beginning with "0x" or "0X" are treated as hexadecimal,
    /// while all other strings are interpreted as decimal.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("0x") || s.starts_with("0X") {
            Self::from_hex_str(s)
        } else {
            Self::from_dec_str(s)
        }
    }
}
