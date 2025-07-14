#[cfg(test)]
mod tests;

use core::{fmt::Debug, str::FromStr};

use crate::felt::{Felt, PrimitiveFromFeltError};

#[derive(Debug)]
pub enum FromStrError {
    ValueTooBig,
    Invalid,
    Parse(<u128 as FromStr>::Err),
}

impl core::fmt::Display for FromStrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FromStrError::ValueTooBig => core::fmt::Display::fmt("value too big for u256", f),
            FromStrError::Parse(e) => {
                // Avoid using format as it requires `alloc`
                core::fmt::Display::fmt("invalid string: ", f)?;
                core::fmt::Display::fmt(e, f)
            }
            FromStrError::Invalid => core::fmt::Display::fmt("invalid characters", f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for FromStrError {}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct U256 {
    high: u128,
    low: u128,
}

impl U256 {
    pub fn high(&self) -> u128 {
        self.high
    }

    pub fn low(&self) -> u128 {
        self.low
    }

    pub fn from_parts(high: u128, low: u128) -> Self {
        Self { low, high }
    }

    pub fn try_from_felt_parts(high: Felt, low: Felt) -> Result<Self, PrimitiveFromFeltError> {
        Ok(Self {
            high: high.try_into()?,
            low: low.try_into()?,
        })
    }

    pub fn try_from_dec_str_parts(high: &str, low: &str) -> Result<Self, <u128 as FromStr>::Err> {
        Ok(Self {
            high: high.parse()?,
            low: low.parse()?,
        })
    }

    pub fn try_from_hex_str_parts(high: &str, low: &str) -> Result<Self, <u128 as FromStr>::Err> {
        Ok(Self {
            high: u128::from_str_radix(high, 16)?,
            low: u128::from_str_radix(low, 16)?,
        })
    }

    pub fn from_hex_str(hex_str: &str) -> Result<Self, FromStrError> {
        let string_without_prefix = if hex_str.starts_with("0x") || hex_str.starts_with("0X") {
            &hex_str[2..]
        } else {
            hex_str
        };

        let string_without_zero_padding = string_without_prefix.trim_start_matches('0');

        let (high, low) = if string_without_zero_padding.is_empty() {
            if string_without_zero_padding.len() == string_without_prefix.len() {
                return Err(FromStrError::Invalid);
            } else {
                (0, 0)
            }
        } else if string_without_zero_padding.len() > 64 {
            return Err(FromStrError::ValueTooBig);
        } else if string_without_zero_padding.len() > 32 {
            let delimiter_index = string_without_zero_padding.len() - 32;
            (
                u128::from_str_radix(&string_without_zero_padding[0..delimiter_index], 16)
                    .map_err(FromStrError::Parse)?,
                u128::from_str_radix(&string_without_zero_padding[delimiter_index..], 16)
                    .map_err(FromStrError::Parse)?,
            )
        } else {
            (
                0,
                u128::from_str_radix(string_without_zero_padding, 16)
                    .map_err(FromStrError::Parse)?,
            )
        };

        Ok(U256 { high, low })
    }

    pub fn from_dec_str(dec_str: &str) -> Result<Self, FromStrError> {
        let string_without_zero_padding = dec_str.trim_start_matches('0');

        let (high, low) = if string_without_zero_padding.is_empty() {
            if string_without_zero_padding.len() == dec_str.len() {
                return Err(FromStrError::Invalid);
            } else {
                (0, 0)
            }
        } else if string_without_zero_padding.len() > 78 {
            return Err(FromStrError::ValueTooBig);
        } else if string_without_zero_padding.len() < 39 {
            (
                0,
                string_without_zero_padding
                    .parse()
                    .map_err(FromStrError::Parse)?,
            )
        } else {
            let mut low = 0u128;
            let mut high = 0u128;
            for b in string_without_zero_padding
                .bytes()
                .map(|b| b.wrapping_sub(b'0'))
            {
                if b > 9 {
                    return Err(FromStrError::Invalid);
                }
                let (new_high, did_overflow) = high.overflowing_mul(10);
                if did_overflow {
                    return Err(FromStrError::ValueTooBig);
                }
                // Long multiplication to get both result and carry
                let (new_low, carry) = {
                    let low_low = low as u64;
                    let low_high = (low >> 64) as u64;

                    let low_low = (low_low as u128) * 10;
                    let low_high = (low_high as u128) * 10;
                    let (result, did_overflow) = low_low.overflowing_add(low_high << 64);
                    // I couldn't come up with a value where `did_overflow` is true,
                    // but better safe than sorry
                    let carry = (low_high >> 64) + if did_overflow { 1 } else { 0 };
                    (result, carry)
                };

                let new_high = if carry != 0 {
                    let (new_high, did_overflow) = new_high.overflowing_add(carry);
                    if did_overflow {
                        return Err(FromStrError::ValueTooBig);
                    }
                    new_high
                } else {
                    new_high
                };

                let (new_low, did_overflow) = new_low.overflowing_add(b.into());
                if did_overflow {
                    let (new_high, carry) = new_high.overflowing_add(1);
                    if carry {
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

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("0x") || s.starts_with("0X") {
            Self::from_hex_str(s)
        } else {
            Self::from_dec_str(s)
        }
    }
}
