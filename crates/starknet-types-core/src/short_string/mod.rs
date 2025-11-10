//! Cairo short string
//!
//! The cairo language make it possible to create `Felt` values at compile time from so-called "short string".
//! See https://docs.starknet.io/archive/cairo-101/strings/ for more information and syntax.
//!
//! This modules allows to mirror this behaviour in Rust, by leveraging type safety.
//! A `ShortString` is string that have been checked and is guaranteed to be convertible into a valid `Felt`.
//! It checks that the `String` only contains ascii characters and is no longer than 31 characters.
//!
//! The convesion to `Felt` is done by using the internal ascii short string as bytes and parse those as a big endian number.

use crate::felt::Felt;
use core::str::FromStr;

#[cfg(not(feature = "std"))]
use crate::felt::alloc::string::{String, ToString};

/// A cairo short string
///
/// Allow for safe conversion of cairo short string `String` into `Felt`,
/// as it is guaranteed that the value it contains can be represented as a felt.
#[repr(transparent)]
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortString(String);

impl core::fmt::Display for ShortString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl ShortString {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl AsRef<str> for ShortString {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl From<ShortString> for Felt {
    fn from(ss: ShortString) -> Self {
        let bytes = ss.0.as_bytes();

        let mut buffer = [0u8; 32];
        // `ShortString` initialization guarantee that the string is ascii and its len doesn't exceed 31.
        // Which mean that its bytes representation won't either exceed 31 bytes.
        // So, this won't panic.
        buffer[(32 - bytes.len())..].copy_from_slice(bytes);

        // The conversion will never fail
        Felt::from_bytes_be(&buffer)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum TryShortStringFromFeltError {
    TooLong(Felt),
    NonAscii(Felt),
}

impl core::fmt::Display for TryShortStringFromFeltError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TryShortStringFromFeltError::TooLong(value) => write!(
                f,
                "felt value `{:#x}` has to many significant bytes, the first one should always be set to zero to represent a 31 chars long string",
                value
            ),
            TryShortStringFromFeltError::NonAscii(value) => {
                write!(f, "felt value `{:#x}` contains non ascii bytes", value)
            }
        }
    }
}

impl TryFrom<Felt> for ShortString {
    type Error = TryShortStringFromFeltError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        let bytes = value.to_bytes_be();
        if bytes[0] != 0 {
            return Err(TryShortStringFromFeltError::TooLong(value));
        }
        let first_non_zero_byte = match bytes.iter().position(|&v| v != 0) {
            Some(i) => i,
            None => return Ok(ShortString(String::new())),
        };
        if !bytes[first_non_zero_byte..].is_ascii() {
            return Err(TryShortStringFromFeltError::NonAscii(value));
        }

        // Safe to use because we already checked all the bytes are valid ascii characters
        let s = unsafe { str::from_utf8_unchecked(&bytes[first_non_zero_byte..]) };

        Ok(ShortString(s.to_string()))
    }
}

#[derive(Debug, Copy, Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum TryShortStringFromStringError {
    TooLong,
    NonAscii,
}

impl core::fmt::Display for TryShortStringFromStringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TryShortStringFromStringError::TooLong => "string too long",
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
    /// Create a felt value from a cairo short string.
    ///
    /// The string must contains only ascii characters
    /// and its length must not exceed 31.
    ///
    /// The returned felt value be that of the input raw bytes.
    pub fn parse_cairo_short_string(string: &str) -> Result<Self, TryShortStringFromStringError> {
        let bytes = string.as_bytes();
        if !bytes.is_ascii() {
            return Err(TryShortStringFromStringError::NonAscii);
        }
        if bytes.len() > 31 {
            return Err(TryShortStringFromStringError::TooLong);
        }

        let mut buffer = [0u8; 32];
        buffer[(32 - bytes.len())..].copy_from_slice(bytes);

        // The conversion will never fail
        Ok(Felt::from_bytes_be(&buffer))
    }
}

impl FromStr for ShortString {
    type Err = TryShortStringFromStringError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if value.len() > 31 {
            return Err(TryShortStringFromStringError::TooLong);
        }
        if !value.is_ascii() {
            return Err(TryShortStringFromStringError::NonAscii);
        }

        Ok(ShortString(value.to_string()))
    }
}

/// Create a `ShortString` at compile time from a string literal.
///
/// This macro validates at compile time that the string:
/// - Contains only ASCII characters
/// - Is no longer than 31 characters
///
/// # Panics
///
/// Panics at compile time if the string is invalid.
///
/// # Examples
///
/// ```
/// use starknet_types_core::{short_string};
///
/// let ss = short_string!("Hello, Cairo!");
/// assert_eq!(ss.to_string(), "Hello, Cairo!");
///
/// // This would fail to compile:
/// // let ss = short_string!("This string is way too long for a Cairo short string");
/// ```
#[macro_export]
macro_rules! short_string {
    ($s:expr) => {{
        const _: () = {
            let bytes = $s.as_bytes();
            assert!(
                bytes.len() <= 31,
                "Short string must be at most 31 characters"
            );
            assert!(
                bytes.is_ascii(),
                "Short string must contain only ASCII characters"
            );
        };

        // Safety: We've validated the string at compile time
        match <$crate::short_string::ShortString as core::str::FromStr>::from_str($s) {
            Ok(ss) => ss,
            Err(_) => unreachable!("compile-time validation should prevent this"),
        }
    }};
}

#[cfg(test)]
mod tests {
    use crate::chain_id::{SN_MAIN, SN_MAIN_STR, SN_SEPOLIA, SN_SEPOLIA_STR};

    use super::*;

    #[test]
    fn test_short_string_macro() {
        let ss = short_string!("test");
        assert_eq!(ss.to_string(), "test");

        let ss = short_string!("SN_MAIN");
        assert_eq!(ss.to_string(), SN_MAIN_STR);

        let ss = short_string!("This is a 31 characters string.");
        assert_eq!(ss.to_string(), "This is a 31 characters string.");

        let ss = short_string!("");
        assert_eq!(ss.to_string(), "");
    }

    #[test]
    fn short_string_and_felt_full_round() {
        let ss1 = ShortString::from_str("A short string").unwrap();
        let f = Felt::from(ss1.clone());
        let ss2 = ShortString::try_from(f).unwrap();

        assert_eq!(ss1, ss2);
    }

    #[test]
    fn chain_ids() {
        let ss = ShortString::try_from(SN_MAIN).unwrap();
        assert_eq!(ss.to_string(), SN_MAIN_STR.to_string());
        let ss = ShortString::try_from(SN_SEPOLIA).unwrap();
        assert_eq!(ss.to_string(), SN_SEPOLIA_STR.to_string());
    }

    #[test]
    fn ok() {
        for (string, expected_felt) in [
            (String::default(), Felt::ZERO),
            (String::from("aa"), Felt::from_hex_unwrap("0x6161")),
            (
                String::from("approve"),
                Felt::from_hex_unwrap("0x617070726f7665"),
            ),
            (
                String::from(SN_SEPOLIA_STR),
                Felt::from_raw([
                    507980251676163170,
                    18446744073709551615,
                    18446744073708869172,
                    1555806712078248243,
                ]),
            ),
        ] {
            let felt = Felt::parse_cairo_short_string(&string).unwrap();
            let short_string = ShortString::try_from(string.clone()).unwrap();

            assert_eq!(felt, expected_felt);
            assert_eq!(short_string.0, string);
            assert_eq!(Felt::from(short_string), expected_felt);
        }
    }

    #[test]
    fn ko_too_long() {
        let ok_string = String::from("This is a 31 characters string.");
        assert!(Felt::parse_cairo_short_string(&ok_string).is_ok());
        let ss = ShortString::try_from(ok_string.clone()).unwrap();
        assert_eq!(ok_string, ss.to_string());

        let ko_string = String::from("This is a 32 characters string..");

        assert_eq!(
            Felt::parse_cairo_short_string(&ko_string),
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
            Felt::parse_cairo_short_string(&string),
            Err(TryShortStringFromStringError::NonAscii)
        );
        assert_eq!(
            ShortString::try_from(string),
            Err(TryShortStringFromStringError::NonAscii)
        );
    }
}
