#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::{Felt};

fuzz_target!(|felt: Felt| {
    assert_eq!(felt, Felt::from_bytes_be(&felt.to_bytes_be()), "to_bytes_be failed");
    assert_eq!(felt, Felt::from_bytes_le(&felt.to_bytes_le()), "to_bytes_le failed");
    assert_eq!(felt, Felt::from_bytes_be_slice(&felt.to_bytes_be()), "to_bytes_be failed");
    assert_eq!(felt, Felt::from_bytes_le_slice(&felt.to_bytes_le()), "to_bytes_be failed");

    assert_eq!(felt, Felt::from_hex_unchecked(&felt.to_hex_string()), "to_hex_string failed");
    assert_eq!(felt, Felt::from_hex_unchecked(&felt.to_fixed_hex_string()), "to_fixed_hex_string failed");
    assert_eq!(66, felt.to_fixed_hex_string().len(), "to_fixed_hex_string failed");
});