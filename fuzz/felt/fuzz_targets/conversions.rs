#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::Felt;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use lambdaworks_math::unsigned_integer::element::UnsignedInteger;

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
    // to_bytes_be, to_bytes_le
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

    // to_hex_string, to_fixed_hex_string, from_hex_unwrap
    assert_eq!(felt, Felt::from_hex_unwrap(&felt.to_hex_string()));
    assert_eq!(felt, Felt::from_hex_unwrap(&felt.to_fixed_hex_string()));
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

    // to_be_digits, to_le_digits
    assert_eq!(
        UnsignedInteger::<4>::from_hex(&felt.to_hex_string()).unwrap(),
        UnsignedInteger::<4>::from_limbs(felt.to_be_digits())
    );
    let mut le_digits_reversed = felt.to_le_digits();
    le_digits_reversed.reverse();
    assert_eq!(
        UnsignedInteger::<4>::from_hex(&felt.to_hex_string()).unwrap(),
        UnsignedInteger::<4>::from_limbs(le_digits_reversed)
    );

    // TryForm unsigned primitives
    if felt <= Felt::from(u8::MAX) {
        assert_eq!(felt, Felt::from(u8::try_from(felt).unwrap()));
    } else {
        assert!(u8::try_from(felt).is_err());
    }
    if felt <= Felt::from(u16::MAX) {
        assert_eq!(felt, Felt::from(u16::try_from(felt).unwrap()));
    } else {
        assert!(u16::try_from(felt).is_err());
    }
    if felt <= Felt::from(u32::MAX) {
        assert_eq!(felt, Felt::from(u32::try_from(felt).unwrap()));
    } else {
        assert!(u32::try_from(felt).is_err());
    }
    if felt <= Felt::from(u64::MAX) {
        assert_eq!(felt, Felt::from(u64::try_from(felt).unwrap()));
    } else {
        assert!(u64::try_from(felt).is_err());
    }
    if felt <= Felt::from(usize::MAX) {
        assert_eq!(felt, Felt::from(usize::try_from(felt).unwrap()));
    } else {
        assert!(usize::try_from(felt).is_err());
    }
    if felt <= Felt::from(u128::MAX) {
        assert_eq!(felt, Felt::from(u128::try_from(felt).unwrap()));
    } else {
        assert!(u128::try_from(felt).is_err());
    }

    // TryFrom signed primitives
    if felt <= Felt::from(i8::MAX) || felt >= Felt::from(i8::MIN) {
        assert_eq!(felt, Felt::from(i8::try_from(felt).unwrap()));
    } else {
        assert!(i8::try_from(felt).is_err());
    }
    if felt <= Felt::from(i16::MAX) || felt >= Felt::from(i16::MIN) {
        assert_eq!(felt, Felt::from(i16::try_from(felt).unwrap()));
    } else {
        assert!(i16::try_from(felt).is_err());
    }
    if felt <= Felt::from(i32::MAX) || felt >= Felt::from(i32::MIN) {
        assert_eq!(felt, Felt::from(i32::try_from(felt).unwrap()));
    } else {
        assert!(i32::try_from(felt).is_err());
    }
    if felt <= Felt::from(i64::MAX) || felt >= Felt::from(i64::MIN) {
        assert_eq!(felt, Felt::from(i64::try_from(felt).unwrap()));
    } else {
        assert!(i64::try_from(felt).is_err());
    }
    if felt <= Felt::from(isize::MAX) || felt >= Felt::from(isize::MIN) {
        assert_eq!(felt, Felt::from(isize::try_from(felt).unwrap()));
    } else {
        assert!(isize::try_from(felt).is_err());
    }
    if felt <= Felt::from(i128::MAX) || felt >= Felt::from(i128::MIN) {
        assert_eq!(felt, Felt::from(i128::try_from(felt).unwrap()));
    } else {
        assert!(i128::try_from(felt).is_err());
    }
});
