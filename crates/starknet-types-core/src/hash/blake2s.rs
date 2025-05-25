use crate::felt::Felt;
use blake2::Blake2s256;
use digest::Digest;

extern crate alloc;
use alloc::vec::Vec;

use super::traits::StarkHash;

pub struct Blake2s;

impl StarkHash for Blake2s {
    fn hash(felt_0: &Felt, felt_1: &Felt) -> Felt {
        Self::hash_array(&[*felt_0, *felt_1])
    }

    fn hash_array(felts: &[Felt]) -> Felt {
        Self::encode_felt252_data_and_calc_224_bit_blake_hash(felts)
    }

    fn hash_single(felt: &Felt) -> Felt {
        Self::hash_array(&[*felt])
    }
}

impl Blake2s {
    // Encode each `Felt` into 32-bit words:
    /// - **Small** values `< 2^63` get **2** words: `[ high_32_bits, low_32_bits ]` from the last 8
    ///   bytes of the 256-bit BE representation.
    /// - **Large** values `>= 2^63` get **8** words: the full 32-byte big-endian split, **with** the
    ///   MSB of the first word set as a marker (`+2^255`).
    ///
    /// # Returns
    /// A flat `Vec<u32>` containing all the unpacked words, in the same order.
    pub fn encode_felts_to_u32s(felts: Vec<Felt>) -> Vec<u32> {
        // 2**63.
        const SMALL_THRESHOLD: Felt = Felt::from_hex_unchecked("8000000000000000");
        // MSB mask for the first u32 in the 8-limb case.
        const BIG_MARKER: u32 = 1 << 31;
        // Number of bytes per u32.
        const BYTES_PER_U32: usize = 4;

        let mut unpacked_u32s = Vec::new();
        for felt in felts {
            let felt_as_be_bytes = felt.to_bytes_be();
            if felt < SMALL_THRESHOLD {
                // small: 2 limbs only, extracts the 8 LSBs.
                let high = u32::from_be_bytes(felt_as_be_bytes[24..28].try_into().unwrap());
                let low = u32::from_be_bytes(felt_as_be_bytes[28..32].try_into().unwrap());
                unpacked_u32s.push(high);
                unpacked_u32s.push(low);
            } else {
                // big: 8 limbs, big‐endian order.
                let start = unpacked_u32s.len();

                for chunk in felt_as_be_bytes.chunks_exact(BYTES_PER_U32) {
                    unpacked_u32s.push(u32::from_be_bytes(chunk.try_into().unwrap()));
                }
                // set the MSB of the very first limb as the Cairo hint does with "+ 2**255".
                unpacked_u32s[start] |= BIG_MARKER;
            }
        }
        unpacked_u32s
    }

    /// Packs the first 7 little-endian 32-bit words (28 bytes) of `bytes`
    /// into a single 224-bit Felt.
    fn pack_224_le_to_felt(bytes: &[u8]) -> Felt {
        assert!(bytes.len() >= 28, "need at least 28 bytes to pack 7 words");

        // 1) copy your 28-byte LE-hash into the low 28 bytes of a 32-byte buffer.
        let mut buf = [0u8; 32];
        buf[..28].copy_from_slice(&bytes[..28]);

        // 2) interpret the whole 32-byte buffer as a little-endian Felt.
        Felt::from_bytes_le(&buf)
    }

    fn blake2s_to_felt(data: &[u8]) -> Felt {
        let mut hasher = Blake2s256::new();
        hasher.update(data);
        let hash32 = hasher.finalize();
        Self::pack_224_le_to_felt(hash32.as_slice())
    }

    /// Encodes a slice of `Felt` values into 32-bit words exactly as Cairo’s
    /// `encode_felt252_to_u32s` hint does, then hashes the resulting byte stream
    /// with Blake2s-256 and returns the 224-bit truncated digest as a `Felt`.
    pub fn encode_felt252_data_and_calc_224_bit_blake_hash(data: &[Felt]) -> Felt {
        // 1) Unpack each Felt into 2 or 8 u32.
        let u32_words = Self::encode_felts_to_u32s(data.to_vec());

        // 2) Serialize the u32 limbs into a little-endian byte stream.
        let mut byte_stream = Vec::with_capacity(u32_words.len() * 4);
        for word in u32_words {
            byte_stream.extend_from_slice(&word.to_le_bytes());
        }

        // 3) Compute Blake2s-256 over the bytes and pack the first 224 bits into a Felt.
        Self::blake2s_to_felt(&byte_stream)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::felt::Felt;

    /// Test two-limb encoding for a small Felt (< 2^63) into high and low 32-bit words.
    #[test]
    fn test_encode_felts_to_u32s_small() {
        // Last 8 bytes of 0x1122334455667788 in big-endian are [0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88].
        // High word = 0x11223344, low word = 0x55667788.
        let val = Felt::from_hex_unchecked("1122334455667788");
        let words = Blake2s::encode_felts_to_u32s(vec![val]);
        assert_eq!(words, vec![0x11223344, 0x55667788]);
    }

    /// Test eight-limb encoding and MSB marker for a big Felt (>= 2^63).
    #[test]
    fn test_encode_felts_to_u32s_big() {
        // The value 2^63 (0x8000000000000000) triggers the "big" path.
        let val = Felt::from_hex_unchecked("8000000000000000");
        let words = Blake2s::encode_felts_to_u32s(vec![val]);

        // Expected limbs: split full 32-byte BE into eight 32-bit words.
        // The seventh BE chunk [0x80,0x00,0x00,0x00] becomes 0x80000000 at index 6.
        // Additionally, set the MSB marker (bit 31) on the first word.
        let mut expected = vec![0u32; 8];
        expected[6] = 0x8000_0000;
        expected[0] |= 1 << 31;
        assert_eq!(words, expected);
    }

    /// Test packing of a 28-byte little-endian buffer into a 224-bit Felt.
    #[test]
    fn test_pack_224_le_to_felt_roundtrip() {
        // Create a 28-byte buffer with values 1..28 and pad to 32 bytes.
        let mut buf = [0u8; 32];
        for i in 0..28 {
            buf[i] = (i + 1) as u8;
        }
        let f = Blake2s::pack_224_le_to_felt(&buf);
        let out = f.to_bytes_le();

        // Low 28 bytes must match the input buffer.
        assert_eq!(&out[..28], &buf[..28]);
        // High 4 bytes must remain zero.
        assert_eq!(&out[28..], &[0, 0, 0, 0]);
    }

    /// Test that pack_224_le_to_felt panics when input is shorter than 28 bytes.
    #[test]
    #[should_panic(expected = "need at least 28 bytes")]
    fn test_pack_224_le_to_felt_too_short() {
        let too_short = [0u8; 27];
        Blake2s::pack_224_le_to_felt(&too_short);
    }

    /// Test that hashing a single zero Felt produces the expected 224-bit Blake2s digest.
    #[test]
    fn test_hash_single_zero() {
        let zero = Felt::from_hex_unchecked("0");
        let hash = Blake2s::hash_single(&zero);
        let expected =
            Felt::from_hex_unchecked("71a2f9bc7c9df9dc4ca0e7a1c5908d5eff88af963c3264f412dbdf50");
        assert_eq!(hash, expected);
    }

    /// Test that hashing an array of Felts [1, 2] produces the expected 224-bit Blake2s digest.
    #[test]
    fn test_hash_array_one_two() {
        let one = Felt::from_hex_unchecked("1");
        let two = Felt::from_hex_unchecked("2");
        let hash = Blake2s::hash_array(&[one, two]);
        let expected =
            Felt::from_hex_unchecked("a14b223236366f30e9c77b6e56c8835de7dc5aee36957d4384cce67b");
        assert_eq!(hash, expected);
    }
}
