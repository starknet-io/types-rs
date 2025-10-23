pub extern crate alloc;

use alloc::format;
use alloc::string::String;
use core::fmt;
use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};
use serde::{
    Deserialize, Serialize,
    de::{self},
};

use super::Felt;

impl Serialize for Felt {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ::serde::Serializer,
    {
        if serializer.is_human_readable() {
            serializer.serialize_str(&format!("{:#x}", self))
        } else {
            let be_bytes = self.to_bytes_be();
            let first_significant_byte_index = be_bytes.iter().position(|&b| b != 0).unwrap_or(31);
            serializer.serialize_bytes(&be_bytes[first_significant_byte_index..])
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
        if value.len() > 32 {
            return Err(de::Error::invalid_length(value.len(), &self));
        }

        let mut buffer = [0u8; 32];
        buffer[32 - value.len()..].copy_from_slice(value);
        Ok(Felt::from_bytes_be(&buffer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bincode::Options;
    use proptest::prelude::*;
    use serde_test::{Configure, Token, assert_tokens};

    #[test]
    fn serde() {
        assert_tokens(&Felt::ZERO.readable(), &[Token::String("0x0")]);
        assert_tokens(&Felt::TWO.readable(), &[Token::String("0x2")]);
        assert_tokens(&Felt::THREE.readable(), &[Token::String("0x3")]);
        assert_tokens(
            &Felt::MAX.readable(),
            &[Token::String(
                "0x800000000000011000000000000000000000000000000000000000000000000",
            )],
        );

        assert_tokens(&Felt::ZERO.compact(), &[Token::Bytes(&[0; 1])]);
        assert_tokens(&Felt::TWO.compact(), &[Token::Bytes(&[2])]);
        assert_tokens(&Felt::THREE.compact(), &[Token::Bytes(&[3])]);
        static MAX: [u8; 32] = [
            8, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        assert_tokens(&Felt::MAX.compact(), &[Token::Bytes(&MAX)]);
        assert_tokens(
            &Felt::from_hex_unwrap("0xbabe").compact(),
            &[Token::Bytes(&[0xba, 0xbe])],
        );
        assert_tokens(
            &Felt::from_hex_unwrap("0xba000000be").compact(),
            &[Token::Bytes(&[0xba, 0, 0, 0, 0xbe])],
        );
        assert_tokens(
            &Felt::from_hex_unwrap("0xbabe0000").compact(),
            &[Token::Bytes(&[0xba, 0xbe, 0, 0])],
        );
    }

    #[test]
    fn backward_compatible_deserialization() {
        static TWO_SERIALIZED_USING_PREVIOUS_IMPLEMENTATION: [u8; 33] = [
            32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 2,
        ];

        let options = bincode::DefaultOptions::new();
        let deserialized = options
            .deserialize(&TWO_SERIALIZED_USING_PREVIOUS_IMPLEMENTATION)
            .unwrap();
        assert_eq!(Felt::TWO, deserialized);
    }

    proptest! {
        #[test]
        fn compact_round_trip(ref x in any::<Felt>()) {
            let serialized = bincode::serialize(&x).unwrap();
            let deserialized: Felt = bincode::deserialize(&serialized).unwrap();
            prop_assert_eq!(x, &deserialized);
        }
    }
}
