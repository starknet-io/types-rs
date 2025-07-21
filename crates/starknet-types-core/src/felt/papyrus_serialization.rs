use std::io::Error;

use super::Felt;
/// Storage efficient serialization for field elements.
impl Felt {
    // Felt encoding constants.
    const CHOOSER_FULL: u8 = 15;
    const CHOOSER_HALF: u8 = 14;
    pub fn serialize(&self, res: &mut impl std::io::Write) -> Result<(), Error> {
        let self_as_bytes = self.to_bytes_be();
        // We use the fact that bytes[0] < 0x10 and encode the size of the felt in the 4 most
        // significant bits of the serialization, which we call `chooser`. We assume that 128 bit
        // felts are prevalent (because of how uint256 is encoded in felts).

        // The first i for which nibbles 2i+1, 2i+2 are nonzero. Note that the first nibble is
        // always 0.
        let mut first_index = 31;
        // Find first non zero byte
        if let Some((index, value)) = self_as_bytes
            .iter()
            .enumerate()
            .find(|(_index, value)| value != &&0u8)
        {
            if value < &16 {
                // Can encode the chooser and the value on a single byte.
                first_index = index;
            } else {
                // The chooser is encoded with the first nibble of the value.
                first_index = index - 1;
            }
        };
        let chooser = if first_index < 15 {
            // For 34 up to 63 nibble felts: chooser == 15, serialize using 32 bytes.
            first_index = 0;
            Felt::CHOOSER_FULL
        } else if first_index < 18 {
            // For 28 up to 33 nibble felts: chooser == 14, serialize using 17 bytes.
            first_index = 15;
            Felt::CHOOSER_HALF
        } else {
            // For up to 27 nibble felts: serialize the lower 1 + (chooser * 2) nibbles of the felt
            // using chooser + 1 bytes.
            (31 - first_index) as u8
        };
        res.write_all(&[(chooser << 4) | self_as_bytes[first_index]])?;
        res.write_all(&self_as_bytes[first_index + 1..])?;
        Ok(())
    }

    /// Storage efficient deserialization for field elements.
    pub fn deserialize(bytes: &mut impl std::io::Read) -> Option<Self> {
        let mut res = [0u8; 32];

        bytes.read_exact(&mut res[..1]).ok()?;
        let first = res[0];
        let chooser: u8 = first >> 4;
        let first = first & 0x0f;

        let first_index = if chooser == Felt::CHOOSER_FULL {
            0
        } else if chooser == Felt::CHOOSER_HALF {
            15
        } else {
            (31 - chooser) as usize
        };
        res[0] = 0;
        res[first_index] = first;
        bytes.read_exact(&mut res[first_index + 1..]).ok()?;
        Some(Self::from_bytes_be(&res))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests proper serialization and deserialization of felts using `parity-scale-codec`.
    #[test]
    fn hash_serde() {
        fn enc_len(n_nibbles: usize) -> usize {
            match n_nibbles {
                0..=27 => n_nibbles / 2 + 1,
                28..=33 => 17,
                _ => 32,
            }
        }

        // 64 nibbles are invalid.
        for n_nibbles in 0..64 {
            let mut bytes = [0u8; 32];
            // Set all nibbles to 0xf.
            for i in 0..n_nibbles {
                bytes[31 - (i >> 1)] |= 15 << (4 * (i & 1));
            }
            let h = Felt::from_bytes_be(&bytes);
            let mut res = Vec::new();
            assert!(h.serialize(&mut res).is_ok());
            assert_eq!(res.len(), enc_len(n_nibbles));
            let mut reader = &res[..];
            let d = Felt::deserialize(&mut reader).unwrap();
            assert_eq!(Felt::from_bytes_be(&bytes), d);
        }
    }
}
