//! Blake2s-256 hash implementation for Starknet field elements.
//!
//! This module implements Blake2s-256 hashing for `Felt` values following the
//! Cairo specification. The implementation includes specific data serialization
//! choices that match the Cairo reference implementation.
//!
//! ## Data Serialization
//!
//! Each `Felt` is encoded into 32-bit words based on its magnitude:
//! - **Small values** (< 2^63): encoded as 2 words from the last 8 bytes
//! - **Large values** (≥ 2^63): encoded as 8 words from the full 32-byte representation,
//!   with the MSB of the first word set as a marker
//!
//! The resulting words are serialized in little-endian byte order before hashing.
//! The Blake2s-256 digest is then packed into a `Felt` using all 256 bits modulo the field prime.
//!
//! ## Reference Implementation
//!
//! This implementation follows the Cairo specification:
//! - [Cairo Blake2s implementation](https://github.com/starkware-libs/cairo-lang/blob/master/src/starkware/cairo/common/cairo_blake2s/blake2s.cairo)

use crate::felt::Felt;
use blake2::Blake2s256;
use digest::Digest;

extern crate alloc;
use alloc::vec::Vec;

use super::traits::StarkHash;

pub struct Blake2Felt252;

impl StarkHash for Blake2Felt252 {
    fn hash(felt_0: &Felt, felt_1: &Felt) -> Felt {
        Self::hash_array(&[*felt_0, *felt_1])
    }

    fn hash_array(felts: &[Felt]) -> Felt {
        Self::encode_felt252_data_and_calc_blake_hash(felts)
    }

    fn hash_single(felt: &Felt) -> Felt {
        Self::hash_array(&[*felt])
    }
}

impl Blake2Felt252 {
    /// Threshold for choosing the encoding strategy of a `Felt`.
    /// Values below `SMALL_THRESHOLD` are encoded as two `u32`s,
    /// while values at or above it are encoded as eight `u32`s
    /// (`SMALL_THRESHOLD` equals `2**63`).
    pub const SMALL_THRESHOLD: Felt = Felt::from_hex_unwrap("8000000000000000");

    /// Encodes each `Felt` into 32-bit words:
    /// - **Small** values `< 2^63` get **2** words: `[ high_32_bits, low_32_bits ]` from the last 8
    ///   bytes of the 256-bit BE representation.
    /// - **Large** values `>= 2^63` get **8** words: the full 32-byte big-endian split, **with** the
    ///   MSB of the first word set as a marker (`+2^255`).
    ///
    /// # Returns
    /// A flat `Vec<u32>` containing all the unpacked words, in the same order.
    pub fn encode_felts_to_u32s(felts: &[Felt]) -> Vec<u32> {
        // MSB mask for the first u32 in the 8-limb case.
        const BIG_MARKER: u32 = 1 << 31;
        // Number of bytes per u32.
        const BYTES_PER_U32: usize = 4;

        let mut unpacked_u32s = Vec::new();
        for felt in felts {
            let felt_as_be_bytes = felt.to_bytes_be();
            if *felt < Self::SMALL_THRESHOLD {
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

    /// Packs the first 8 little-endian 32-bit words (32 bytes) of `bytes`
    /// into a single 252-bit Felt.
    fn pack_256_le_to_felt(bytes: &[u8]) -> Felt {
        assert!(bytes.len() >= 32, "need at least 32 bytes to pack 8 words");

        // 1) copy your 32-byte LE-hash into the low 32 bytes of a 32-byte buffer.
        let mut buf = [0u8; 32];
        buf[..32].copy_from_slice(&bytes[..32]);

        // 2) interpret the whole 32-byte buffer as a little-endian Felt.
        Felt::from_bytes_le(&buf)
    }

    /// Hashes the data with Blake2s-256 and packs the result into a Felt.
    pub fn hash_and_pack_to_felt(data: &[u8]) -> Felt {
        let mut hasher = Blake2s256::new();
        hasher.update(data);
        let hash32 = hasher.finalize();
        Self::pack_256_le_to_felt(hash32.as_slice())
    }

    /// Encodes a slice of `Felt` values into 32-bit words exactly as Cairo's
    /// [`encode_felt252_to_u32s`](https://github.com/starkware-libs/cairo-lang/blob/ab8be40403a7634ba296c467b26b8bd945ba5cfa/src/starkware/cairo/common/cairo_blake2s/blake2s.cairo)
    /// hint does, then hashes the resulting byte stream with Blake2s-256 and
    /// returns the full 256-bit digest as a `Felt`.
    pub fn encode_felt252_data_and_calc_blake_hash(data: &[Felt]) -> Felt {
        // 1) Unpack each Felt into 2 or 8 u32.
        let u32_words = Self::encode_felts_to_u32s(data);

        // 2) Serialize the u32 limbs into a little-endian byte stream.
        let mut byte_stream = Vec::with_capacity(u32_words.len() * 4);
        for word in u32_words {
            byte_stream.extend_from_slice(&word.to_le_bytes());
        }

        // 3) Compute Blake2s-256 over the bytes and pack the result into a Felt.
        Self::hash_and_pack_to_felt(&byte_stream)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::felt::Felt;
    use rstest::rstest;

    /// Test two-limb encoding for a small Felt (< 2^63) into high and low 32-bit words.
    #[test]
    fn test_encode_felts_to_u32s_small() {
        // Last 8 bytes of 0x1122334455667788 in big-endian are [0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88].
        // High word = 0x11223344, low word = 0x55667788.
        let val = Felt::from_hex_unwrap("1122334455667788");
        let words = Blake2Felt252::encode_felts_to_u32s(&[val]);
        assert_eq!(words, vec![0x11223344, 0x55667788]);
    }

    /// Test eight-limb encoding and MSB marker for a big Felt (>= 2^63).
    #[test]
    fn test_encode_felts_to_u32s_big() {
        // The value 2^63 (0x8000000000000000) triggers the "big" path.
        let val = Felt::from_hex_unwrap("8000000000000000");
        let words = Blake2Felt252::encode_felts_to_u32s(&[val]);

        // Expected limbs: split full 32-byte BE into eight 32-bit words.
        // The seventh BE chunk [0x80,0x00,0x00,0x00] becomes 0x80000000 at index 6.
        // Additionally, set the MSB marker (bit 31) on the first word.
        let mut expected = vec![0u32; 8];
        expected[6] = 0x8000_0000;
        expected[0] |= 1 << 31;
        assert_eq!(words, expected);
    }

    /// Test packing of a 32-byte little-endian buffer into a 256-bit Felt.
    #[test]
    fn test_pack_256_le_to_felt_basic() {
        // Test with small values that won't trigger modular reduction.
        let mut buf = [0u8; 32];
        buf[0] = 0x01;
        buf[1] = 0x02;
        buf[2] = 0x03;
        buf[3] = 0x04;
        // Leave the rest as zeros.

        let f = Blake2Felt252::pack_256_le_to_felt(&buf);
        let out = f.to_bytes_le();

        // For small values, the first few bytes should match exactly.
        assert_eq!(out[0], 0x01);
        assert_eq!(out[1], 0x02);
        assert_eq!(out[2], 0x03);
        assert_eq!(out[3], 0x04);

        // Test that the packing formula works correctly for a simple case.
        let expected = Felt::from(0x01)
            + Felt::from(0x02) * Felt::from(1u64 << 8)
            + Felt::from(0x03) * Felt::from(1u64 << 16)
            + Felt::from(0x04) * Felt::from(1u64 << 24);
        assert_eq!(f, expected);

        // Test with a value that exceeds the field prime P to verify modular reduction.
        // Create a 32-byte buffer with all 0xFF bytes, representing 2^256 - 1.
        let max_buf = [0xFF_u8; 32];
        let f_max = Blake2Felt252::pack_256_le_to_felt(&max_buf);

        // The result should be (2^256 - 1) mod P.
        // Since 2^256 = Felt::TWO.pow(256), we can compute this value directly.
        // This tests that modular reduction works correctly when exceeding the field prime.
        let two_pow_256_minus_one = Felt::TWO.pow(256u32) - Felt::ONE;
        assert_eq!(f_max, two_pow_256_minus_one);
    }

    /// Test that pack_256_le_to_felt panics when input is shorter than 32 bytes.
    #[test]
    #[should_panic(expected = "need at least 32 bytes to pack 8 words")]
    fn test_pack_256_le_to_felt_too_short() {
        let too_short = [0u8; 31];
        Blake2Felt252::pack_256_le_to_felt(&too_short);
    }

    /// Test that hashing a single zero Felt produces the expected 256-bit Blake2s digest.
    #[test]
    fn test_hash_single_zero() {
        let zero = Felt::from_hex_unwrap("0");
        let hash = Blake2Felt252::hash_single(&zero);
        let expected = Felt::from_hex_unwrap(
            "5768af071a2f8df7c9df9dc4ca0e7a1c5908d5eff88af963c3264f412dbdf43",
        );
        assert_eq!(hash, expected);
    }

    /// Test that hashing an array of Felts [1, 2] produces the expected 256-bit Blake2s digest.
    #[test]
    fn test_hash_array_one_two() {
        let one = Felt::from_hex_unwrap("1");
        let two = Felt::from_hex_unwrap("2");
        let hash = Blake2Felt252::hash_array(&[one, two]);
        let expected = Felt::from_hex_unwrap(
            "5534c03a14b214436366f30e9c77b6e56c8835de7dc5aee36957d4384cce66d",
        );
        assert_eq!(hash, expected);
    }

    /// Test the encode_felt252_data_and_calc_blake_hash function
    /// with the same result as the Cairo v0.14 version.
    #[rstest]
    #[case::empty(vec![], "874258848688468311465623299960361657518391155660316941922502367727700287818")]
    #[case::boundary_under_2_63(vec![Felt::from((1u64 << 63) - 1)], "94160078030592802631039216199460125121854007413180444742120780261703604445")]
    #[case::boundary_at_2_63(vec![Felt::from(1u64 << 63)], "318549634615606806810268830802792194529205864650702991817600345489579978482")]
    #[case::very_large_felt(vec![Felt::from_hex_unwrap("800000000000011000000000000000000000000000000000000000000000000")], "3505594194634492896230805823524239179921427575619914728883524629460058657521")]
    #[case::mixed_small_large(vec![Felt::from(42), Felt::from(1u64 << 63), Felt::from(1337)], "1127477916086913892828040583976438888091205536601278656613505514972451246501")]
    #[case::max_u64(vec![Felt::from(u64::MAX)], "3515074221976790747383295076946184515593027667350620348239642126105984996390")]
    fn test_encode_felt252_data_and_calc_blake_hash(
        #[case] input: Vec<Felt>,
        #[case] expected_result: &str,
    ) {
        let result = Blake2Felt252::encode_felt252_data_and_calc_blake_hash(&input);
        let expected = Felt::from_dec_str(expected_result).unwrap();
        assert_eq!(
            result, expected,
            "rust_implementation: {result:?} != cairo_implementation: {expected:?}"
        );
    }
}
