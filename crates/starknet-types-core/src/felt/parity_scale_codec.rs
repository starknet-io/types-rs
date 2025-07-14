use crate::felt::Felt;

/// Allows transparent binary serialization of Felts with `parity_scale_codec`.
impl parity_scale_codec::Encode for Felt {
    fn encode_to<T: parity_scale_codec::Output + ?Sized>(&self, dest: &mut T) {
        dest.write(&self.to_bytes_be());
    }
}

/// Allows transparent binary deserialization of Felts with `parity_scale_codec`
impl parity_scale_codec::Decode for Felt {
    fn decode<I: parity_scale_codec::Input>(
        input: &mut I,
    ) -> Result<Self, parity_scale_codec::Error> {
        let mut buf: [u8; 32] = [0; 32];
        input.read(&mut buf)?;
        Ok(Felt::from_bytes_be(&buf))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
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
}
