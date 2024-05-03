#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::Felt;

use num_bigint::BigUint;
use num_traits::{One, Zero};

fn pad_left_with_0(v: Vec<u8>) -> Vec<u8> {
    let mut padded = vec![0; 32_usize.saturating_sub(v.len())];
    padded.extend(v);
    padded
}

fn pad_right_with_0(v: Vec<u8>) -> Vec<u8> {
    let padded = vec![0; 32_usize.saturating_sub(v.len())];
    [v, padded].concat()
}

fuzz_target!(|felt: Felt| {
    // to_bytes_be and to_bytes_le
    assert_eq!(felt, Felt::from_bytes_be(&felt.to_bytes_be()));
    assert_eq!(felt, Felt::from_bytes_le(&felt.to_bytes_le()));
    assert_eq!(felt, Felt::from_bytes_be_slice(&felt.to_bytes_be()));
    assert_eq!(felt, Felt::from_bytes_le_slice(&felt.to_bytes_le()));

    // to_bits_be
    let felt_as_bits = &felt.to_bits_be();
    let felt_as_buint = felt.to_biguint();
    for i in 0..256 {
        let bit = (&felt_as_buint & (BigUint::one() << i)) != BigUint::zero();
        assert_eq!(felt_as_bits[255 - i], bit);
    }

    // to_bits_le
    let felt_as_bits = &felt.to_bits_le();
    for i in 0..256 {
        let bit = (&felt_as_buint & (BigUint::one() << i)) != BigUint::zero();
        assert_eq!(felt_as_bits[i], bit);
    }

    // to_hex_string, to_fixed_hex_string, from_hex_unchecked
    assert_eq!(felt, Felt::from_hex_unchecked(&felt.to_hex_string()));
    assert_eq!(felt, Felt::from_hex_unchecked(&felt.to_fixed_hex_string()));
    assert_eq!(66, felt.to_fixed_hex_string().len());

    // from_dec_str
    assert_eq!(
        felt,
        Felt::from_dec_str(&felt_as_buint.to_string()).unwrap()
    );

    // to_bytes_be, to_bytes_le, to_big_uint
    assert_eq!(
        felt.to_bytes_be().to_vec(),
        pad_left_with_0(felt_as_buint.to_bytes_be())
    );
    assert_eq!(
        felt.to_bytes_le().to_vec(),
        pad_right_with_0(felt_as_buint.to_bytes_le())
    );

    // to_raw, from_raw
    assert_eq!(felt, Felt::from_raw(felt.to_raw()));
});
