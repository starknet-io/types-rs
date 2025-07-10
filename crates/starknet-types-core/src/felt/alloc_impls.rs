use core::fmt;

use super::alloc;
use super::Felt;

impl Felt {
    /// Helper to represent the felt value as a zero-padded hexadecimal string.
    ///
    /// Equivalent to calling `format!("{self:#x}")`.
    pub fn to_hex_string(&self) -> alloc::string::String {
        alloc::format!("{self:#x}")
    }

    /// Helper to represent the felt value as a zero-padded hexadecimal string.
    ///
    /// The resulting string will consist of:
    /// 1. A`0x` prefix,
    /// 2. an amount of padding zeros so that the resulting string length is fixed (This amount may be 0),
    /// 3. the felt value represented in hexadecimal
    ///
    /// The resulting string is guaranted to be 66 chars long, which is enough to represent `Felt::MAX`:
    /// 2 chars for the `0x` prefix and 64 chars for the padded hexadecimal felt value.
    pub fn to_fixed_hex_string(&self) -> alloc::string::String {
        let hex_str = alloc::format!("{self:#x}");
        if hex_str.len() < 66 {
            alloc::format!("0x{:0>64}", hex_str.strip_prefix("0x").unwrap())
        } else {
            hex_str
        }
    }
}

/// Represents [Felt] in lowercase hexadecimal format.
impl fmt::LowerHex for Felt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hex = alloc::string::ToString::to_string(&self.0);
        let hex = hex.strip_prefix("0x").unwrap();

        let width = if f.sign_aware_zero_pad() {
            f.width().unwrap().min(64)
        } else {
            1
        };
        if f.alternate() {
            write!(f, "0x")?;
        }

        if hex.len() < width {
            for _ in 0..(width - hex.len()) {
                write!(f, "0")?;
            }
        }
        write!(f, "{}", hex)
    }
}

/// Represents [Felt] in uppercase hexadecimal format.
impl fmt::UpperHex for Felt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hex = alloc::string::ToString::to_string(&self.0);
        let hex = hex.strip_prefix("0x").unwrap().to_uppercase();

        let width = if f.sign_aware_zero_pad() {
            f.width().unwrap().min(64)
        } else {
            1
        };
        if f.alternate() {
            write!(f, "0x")?;
        }

        if hex.len() < width {
            for _ in 0..(width - hex.len()) {
                write!(f, "0")?;
            }
        }
        write!(f, "{}", hex)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn to_hex_string_is_same_as_format(ref x in any::<Felt>()) {
            let y = alloc::format!("{x:#x}");
            prop_assert_eq!(y, x.to_hex_string());
        }
    }
}
