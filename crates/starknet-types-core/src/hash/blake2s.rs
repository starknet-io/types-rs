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
    pub const SMALL_THRESHOLD: Felt = Felt::from_hex_unchecked("8000000000000000");

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
                for chunk in felt_as_be_bytes.chunks_exact(BYTES_PER_U32) {
                    unpacked_u32s.push(u32::from_be_bytes(chunk.try_into().unwrap()));
                }
                // set the MSB of the **entire 256-bit number**
                unpacked_u32s[0] |= BIG_MARKER;
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

    fn blake2s_to_felt(data: &[u8]) -> Felt {
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

        // 3) Compute Blake2s-256 over the bytes and pack the first 256 bits into a Felt.
        Self::blake2s_to_felt(&byte_stream)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::felt::Felt;
    use rstest::rstest;

    #[test]
    fn test_encode_felts_to_u32s_small() {
        let val = Felt::from_hex_unchecked("1122334455667788");
        let words = Blake2Felt252::encode_felts_to_u32s(&[val]);
        assert_eq!(words, vec![0x11223344, 0x55667788]);
    }

    #[test]
    fn test_encode_felts_to_u32s_big() {
        let val = Felt::from_hex_unchecked("8000000000000000");
        let words = Blake2Felt252::encode_felts_to_u32s(&[val]);

        let mut expected = vec![0u32; 8];
        expected[0] |= 0x8000_0000;
        expected[7] = 0x8000_0000;
        assert_eq!(words, expected);
    }

    #[test]
    fn test_pack_256_le_to_felt_basic() {
        let mut buf = [0u8; 32];
        buf[0] = 0x01;
        buf[1] = 0x02;
        buf[2] = 0x03;
        buf[3] = 0x04;

        let f = Blake2Felt252::pack_256_le_to_felt(&buf);
        let out = f.to_bytes_le();

        assert_eq!(out[0], 0x01);
        assert_eq!(out[1], 0x02);
        assert_eq!(out[2], 0x03);
        assert_eq!(out[3], 0x04);

        let expected = Felt::from(0x01)
            + Felt::from(0x02) * Felt::from(1u64 << 8)
            + Felt::from(0x03) * Felt::from(1u64 << 16)
            + Felt::from(0x04) * Felt::from(1u64 << 24);
        assert_eq!(f, expected);

        let max_buf = [0xFF_u8; 32];
        let f_max = Blake2Felt252::pack_256_le_to_felt(&max_buf);

        let two_pow_256_minus_one = Felt::TWO.pow(256u32) - Felt::ONE;
        assert_eq!(f_max, two_pow_256_minus_one);
    }

    #[test]
    #[should_panic(expected = "need at least 32 bytes to pack 8 words")]
    fn test_pack_256_le_to_felt_too_short() {
        let too_short = [0u8; 31];
        Blake2Felt252::pack_256_le_to_felt(&too_short);
    }

    #[test]
    fn test_hash_single_zero() {
        let zero = Felt::from_hex_unchecked("0");
        let hash = Blake2Felt252::hash_single(&zero);
        let expected = Felt::from_hex_unchecked(
            "5768af071a2f8df7c9df9dc4ca0e7a1c5908d5eff88af963c3264f412dbdf43",
        );
        assert_eq!(hash, expected);
    }

    #[test]
    fn test_hash_array_one_two() {
        let one = Felt::from_hex_unchecked("1");
        let two = Felt::from_hex_unchecked("2");
        let hash = Blake2Felt252::hash_array(&[one, two]);
        let expected = Felt::from_hex_unchecked(
            "5534c03a14b214436366f30e9c77b6e56c8835de7dc5aee36957d4384cce66d",
        );
        assert_eq!(hash, expected);
    }

    #[rstest]
    #[case::empty(vec![], "874258848688468311465623299960361657518391155660316941922502367727700287818")]
    #[case::boundary_under_2_63(vec![Felt::from((1u64 << 63) - 1)], "94160078030592802631039216199460125121854007413180444742120780261703604445")]
    #[case::boundary_at_2_63(vec![Felt::from(1u64 << 63)], "318549634615606806810268830802792194529205864650702991817600345489579978482")]
    #[case::very_large_felt(vec![Felt::from_hex_unchecked("800000000000011000000000000000000000000000000000000000000000000")], "3505594194634492896230805823524239179921427575619914728883524629460058657521")]
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
