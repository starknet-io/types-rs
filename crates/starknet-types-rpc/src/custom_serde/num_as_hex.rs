use alloc::vec::Vec;
use core::marker::PhantomData;

/// A trait for types that should be serialized or deserialized as hexadecimal strings.
pub trait NumAsHex<'de>: Sized {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer;

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>;
}

impl<'de> NumAsHex<'de> for u64 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        /// The symbols to be used for the hexadecimal representation.
        const HEX_DIGITS: [u8; 16] = *b"0123456789abcdef";

        if *self == 0 {
            return serializer.serialize_str("0x0");
        }

        // The following code can be very much optimized simply by making everything
        // `unsafe` and using pointers to write to the buffer.
        // Let's benchmark it first to ensure that it's actually worth it.

        // The buffer is filled from the end to the beginning.
        // We know that it will always have the correct size because we made it have the
        // maximum possible size for a base-16 representation of a `u64`.
        //
        // +-----------------------------------+
        // +                           1 2 f a +
        // +-----------------------------------+
        //                           ^ cursor
        //
        // Once the number has been written to the buffer, we simply add a `0x` prefix
        // to the beginning of the buffer. Just like the digits, we know the buffer is
        // large enough to hold the prefix.
        //
        // +-----------------------------------+
        // +                       0 x 1 2 f a +
        // +-----------------------------------+
        //                       ^ cursor
        // |-----------------------| remaining
        //
        // The output string is the part of the buffer that has been written. In other
        // words, we have to skip all the bytes that *were not* written yet (remaining).

        let mut buffer = [0u8; 18]; // Enough for "0x" prefix and 16 hex digits
        let mut n = *self;
        let mut length = 0;

        while n != 0 {
            length += 1;
            buffer[18 - length] = HEX_DIGITS[(n % 16) as usize];
            n /= 16;
        }

        buffer[18 - length - 1] = b'x';
        buffer[18 - length - 2] = b'0';
        length += 2;

        let hex_str = core::str::from_utf8(&buffer[18 - length..]).unwrap();
        serializer.serialize_str(hex_str)
    }

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct NumAsHexVisitor;

        impl<'de> serde::de::Visitor<'de> for NumAsHexVisitor {
            type Value = u64;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a hexadecimal string")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                // Just like the serialization code, this can be further optimized using
                // unsafe code and pointers. Though the gain will probably be less interesting.

                // Explicitly avoid being UTF-8 aware.
                let bytes = v.as_bytes();

                // If the input string does not start with the `0x` prefix, then it's an
                // error. The `NUM_AS_HEX` regex defined in the specification specifies
                // this prefix as mandatory.
                if bytes.len() < 2 || &bytes[0..2] != b"0x" {
                    return Err(E::custom("expected a hexadecimal string starting with 0x"));
                }

                // Aggregate the digits into `n`,
                // Digits from `0` to `9` represent numbers from `0` to `9`.
                // Letters from `a` to `f` represent numbers from `10` to `15`.
                //
                // As specified in the spec, both uppercase and lowercase characters are
                // allowed.
                //
                // Because we already checked the size of the string earlier, we know that
                // the following code will never overflow.
                let hex_bytes = &bytes[2..];

                // Trim leading zeros from the hexadecimal part for efficient processing
                let trimmed_hex = hex_bytes
                    .iter()
                    .skip_while(|&&b| b == b'0')
                    .collect::<Vec<_>>();

                // Check if the significant part of the hexadecimal string is too long for a 64-bit number
                if trimmed_hex.len() > 16 {
                    return Err(E::custom("hexadecimal string too long for a 64-bit number"));
                }

                let mut n = 0u64;
                for &b in &trimmed_hex {
                    let digit = match b {
                        b'0'..=b'9' => b - b'0',
                        b'a'..=b'f' => 10 + b - b'a',
                        b'A'..=b'F' => 10 + b - b'A',
                        _ => return Err(E::custom("invalid hexadecimal digit")),
                    };
                    n = n * 16 + digit as u64;
                }

                Ok(n)
            }
        }

        deserializer.deserialize_str(NumAsHexVisitor)
    }
}

impl<'de, T> NumAsHex<'de> for Option<T>
where
    T: NumAsHex<'de>,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            None => serializer.serialize_none(),
            Some(v) => v.serialize(serializer),
        }
    }

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct OptionVisitor<T>(PhantomData<T>);

        impl<'de, T> serde::de::Visitor<'de> for OptionVisitor<T>
        where
            T: NumAsHex<'de>,
        {
            type Value = Option<T>;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                writeln!(formatter, "an optional number as a hexadecimal string")
            }

            fn visit_none<E>(self) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(None)
            }

            fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                T::deserialize(deserializer).map(Some)
            }
        }

        deserializer.deserialize_option(OptionVisitor(PhantomData))
    }
}

#[cfg(test)]
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
struct Helper {
    #[serde(with = "NumAsHex")]
    num: u64,
}

#[cfg(test)]
fn serialize(num: u64) -> serde_json::Result<alloc::string::String> {
    let helper = Helper { num };
    serde_json::to_string(&helper)
}

#[cfg(test)]
fn deserialize(s: &str) -> serde_json::Result<u64> {
    let helper: Helper = serde_json::from_str(s)?;
    Ok(helper.num)
}

#[test]
#[cfg(test)]
fn serialize_0_hex() {
    assert_eq!(serialize(0x0).unwrap(), "\"0x0\"");
}

#[test]
#[cfg(test)]
fn srialize_hex() {
    assert_eq!(serialize(0x1234).unwrap(), "\"0x1234\"");
}

#[test]
#[cfg(test)]
fn srialize_max() {
    assert_eq!(serialize(u64::MAX).unwrap(), "\"0xffffffffffffffff\"");
}

#[test]
#[cfg(test)]
fn deserialize_zero() {
    assert_eq!(deserialize("\"0x0\"").unwrap(), 0);
}

#[test]
#[cfg(test)]
fn deserialize_zeros() {
    assert_eq!(deserialize("\"0x00000\"").unwrap(), 0);
}

#[test]
#[cfg(test)]
fn deserialize_max() {
    assert_eq!(deserialize("\"0xFFFFFFFFFFFFFFFF\"").unwrap(), u64::MAX);
}

#[test]
#[cfg(test)]
fn deserialize_big_one() {
    assert_eq!(
        deserialize("\"0x000000000000000000000000000001\"").unwrap(),
        1
    );
}

#[test]
#[cfg(test)]
fn deserialize_hex() {
    assert_eq!(deserialize("\"0x1234\"").unwrap(), 0x1234);
}
