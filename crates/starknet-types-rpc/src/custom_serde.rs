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
        const HEX_DIGITS: &[u8] = b"0123456789abcdef";
        const MAX_NUMBER_SIZE: usize = u64::MAX.ilog(16) as usize + 1;

        // This can be very much optimized using unsafe code.
        // Let's benchmark it first to ensure that it's actually worth it.

        let mut buffer = [0u8; MAX_NUMBER_SIZE + 2]; // + 2 to account for 0x
        let mut cursor = buffer.iter_mut().rev();
        let mut n = *self;
        while n != 0 {
            *cursor.next().unwrap() = HEX_DIGITS[(n % 16) as usize];
            n /= 16;
        }
        *cursor.next().unwrap() = b'x';
        *cursor.next().unwrap() = b'0';

        let remaining = cursor.len();

        // SAFETY:
        //  We only wrote ASCII characters to the buffer, ensuring that it is only composed
        //  of valid UTF-8 code points.
        let s = core::str::from_utf8(&buffer[remaining..]).unwrap();

        serializer.serialize_str(s)
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
                let Some(digits) = v.strip_prefix("0x") else {
                    return Err(E::custom("expected a hexadecimal string starting with 0x"));
                };

                let mut n = 0u64;
                for b in digits.bytes() {
                    let unit = match b {
                        b'0'..=b'9' => b as u64 - b'0' as u64,
                        b'a'..=b'f' => b as u64 - b'a' as u64 + 10,
                        b'A'..=b'F' => b as u64 - b'A' as u64 + 10,
                        _ => return Err(E::custom("invalid hexadecimal digit")),
                    };

                    let Some(next_n) = n.checked_mul(16).and_then(|n| n.checked_add(unit)) else {
                        return Err(E::custom("integer overflowed 64-bit"));
                    };

                    n = next_n;
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
