use core::fmt;
use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};
use serde::{de, Deserialize, Serialize};

use super::Felt;

impl Serialize for Felt {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ::serde::Serializer,
    {
        if serializer.is_human_readable() {
            serializer.serialize_str(&format!("{:#x}", self))
        } else {
            serializer.serialize_bytes(&self.to_bytes_be())
        }
    }
}

impl<'de> Deserialize<'de> for Felt {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: ::serde::Deserializer<'de>,
    {
        if deserializer.is_human_readable() {
            deserializer.deserialize_str(FeltVisitor)
        } else {
            deserializer.deserialize_bytes(FeltVisitor)
        }
    }
}

struct FeltVisitor;

impl de::Visitor<'_> for FeltVisitor {
    type Value = Felt;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The message below is append to “This Visitor expects to receive …”
        write!(
            formatter,
            "a 32 byte array ([u8;32]) or a hexadecimal string."
        )
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
            .ok_or(String::from("expected hex string to be prefixed by '0x'"))
            .map_err(de::Error::custom)
    }

    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        match value.try_into() {
            Ok(v) => Ok(Felt::from_bytes_be(&v)),
            _ => Err(de::Error::invalid_length(value.len(), &self)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serde() {
        use serde_test::{assert_tokens, Configure, Token};

        assert_tokens(&Felt::ZERO.readable(), &[Token::String("0x0")]);
        assert_tokens(&Felt::TWO.readable(), &[Token::String("0x2")]);
        assert_tokens(&Felt::THREE.readable(), &[Token::String("0x3")]);
        assert_tokens(
            &Felt::MAX.readable(),
            &[Token::String(
                "0x800000000000011000000000000000000000000000000000000000000000000",
            )],
        );

        assert_tokens(&Felt::ZERO.compact(), &[Token::Bytes(&[0; 32])]);
        static TWO: [u8; 32] = [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 2,
        ];
        assert_tokens(&Felt::TWO.compact(), &[Token::Bytes(&TWO)]);
        static THREE: [u8; 32] = [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 3,
        ];
        assert_tokens(&Felt::THREE.compact(), &[Token::Bytes(&THREE)]);
        static MAX: [u8; 32] = [
            8, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        assert_tokens(&Felt::MAX.compact(), &[Token::Bytes(&MAX)]);
    }
}
