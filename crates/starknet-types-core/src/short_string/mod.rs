//! Cairo short string
//!
//! The cairo language make it possible to create `Felt` values at compile time from so-called "short string".
//! See https://docs.starknet.io/archive/cairo-101/strings/ for more information and syntax.
//!
//! This modules allows to mirror this behaviour in Rust, by leveraging type safety.
//! A `ShortString` is string that have been checked and is guaranted to be convertible into a valid `Felt`.
//! It checks that the `String` only contains ascii characters and is no longer than 31 characters.
//!
//! The convesion to `Felt` is done by using the internal ascii short string as bytes and parse those as a big endian number.

use crate::felt::alloc::string::{String, ToString};
use crate::felt::Felt;

/// A cairo short string
///
/// Allow for safe conversion of cairo short string `String` into `Felt`,
/// as it is guaranted that the value it contains can be represented as a felt.
#[repr(transparent)]
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortString(String);

impl core::fmt::Display for ShortString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl From<ShortString> for Felt {
    fn from(ss: ShortString) -> Self {
        let bytes = ss.0.as_bytes();

        let mut buffer = [0u8; 32];
        buffer[(32 - bytes.len())..].copy_from_slice(bytes);

        // The conversion will never fail
        Felt::from_bytes_be(&buffer)
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum TryShortStringFromStringError {
    TooLong,
    NonAscii,
}

impl core::fmt::Display for TryShortStringFromStringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TryShortStringFromStringError::TooLong => "string to long",
            TryShortStringFromStringError::NonAscii => "string contains non ascii characters",
        }
        .fmt(f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryShortStringFromStringError {}

impl TryFrom<String> for ShortString {
    type Error = TryShortStringFromStringError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        if value.len() > 31 {
            return Err(TryShortStringFromStringError::TooLong);
        }
        if !value.as_str().is_ascii() {
            return Err(TryShortStringFromStringError::NonAscii);
        }

        Ok(ShortString(value))
    }
}

impl Felt {
    /// Create a felt value from a cairo short string
    ///
    /// The string must contains only ascii characters
    /// and its length must not exceed 31.
    pub fn try_from_cairo_short_string(
        string: &str,
    ) -> Result<Self, TryShortStringFromStringError> {
        if string.len() > 31 {
            return Err(TryShortStringFromStringError::TooLong);
        }
        let bytes = string.as_bytes();
        if !bytes.is_ascii() {
            return Err(TryShortStringFromStringError::NonAscii);
        }

        let mut buffer = [0u8; 32];
        buffer[(32 - bytes.len())..].copy_from_slice(bytes);

        // The conversion will never fail
        Ok(Felt::from_bytes_be(&buffer))
    }
}

impl TryFrom<&str> for ShortString {
    type Error = TryShortStringFromStringError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if value.len() > 31 {
            return Err(TryShortStringFromStringError::TooLong);
        }
        if !value.is_ascii() {
            return Err(TryShortStringFromStringError::NonAscii);
        }

        Ok(ShortString(value.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        felt::Felt,
        short_string::{ShortString, TryShortStringFromStringError},
    };

    #[test]
    fn ok() {
        for (string, expected_felt) in [
            (String::default(), Felt::ZERO),
            (String::from("aa"), Felt::from_hex_unchecked("0x6161")),
            (
                String::from("approve"),
                Felt::from_hex_unchecked("0x617070726f7665"),
            ),
            (
                String::from("SN_SEPOLIA"),
                Felt::from_raw([
                    507980251676163170,
                    18446744073709551615,
                    18446744073708869172,
                    1555806712078248243,
                ]),
            ),
        ] {
            let felt = Felt::try_from_cairo_short_string(&string).unwrap();
            let short_string = ShortString::try_from(string.clone()).unwrap();

            assert_eq!(felt, expected_felt);
            assert_eq!(short_string.0, string);
            assert_eq!(Felt::from(short_string), expected_felt);
        }
    }

    #[test]
    fn ko_too_long() {
        let ok_string = String::from("This is a 31 characters string.");
        assert!(Felt::try_from_cairo_short_string(&ok_string).is_ok());
        assert!(ShortString::try_from(ok_string).is_ok());

        let ko_string = String::from("This is a 32 characters string..");

        assert_eq!(
            Felt::try_from_cairo_short_string(&ko_string),
            Err(TryShortStringFromStringError::TooLong)
        );
        assert_eq!(
            ShortString::try_from(ko_string),
            Err(TryShortStringFromStringError::TooLong)
        );
    }

    #[test]
    fn ko_non_ascii() {
        let string = String::from("What a nice emoji 💫");

        assert_eq!(
            Felt::try_from_cairo_short_string(&string),
            Err(TryShortStringFromStringError::NonAscii)
        );
        assert_eq!(
            ShortString::try_from(string),
            Err(TryShortStringFromStringError::NonAscii)
        );
    }
}
