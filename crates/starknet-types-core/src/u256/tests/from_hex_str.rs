use crate::u256::{FromStrError, U256};

#[test]
fn test_from_hex_str_zero_values() {
    // Test "0x0"
    let result = U256::from_hex_str("0x0").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);

    // Test "0X0" (uppercase prefix)
    let result = U256::from_hex_str("0X0").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);

    // Test "0" (no prefix)
    let result = U256::from_hex_str("0").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);

    // Test multiple zeros with prefix
    let result = U256::from_hex_str("0x000").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);

    // Test multiple zeros without prefix
    let result = U256::from_hex_str("000").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);
}

#[test]
fn test_from_hex_str_invalid_empty_after_prefix() {
    // Test empty string after removing prefix and zeros
    assert!(matches!(
        U256::from_hex_str("0x"),
        Err(FromStrError::Invalid)
    ));

    assert!(matches!(
        U256::from_hex_str("0X"),
        Err(FromStrError::Invalid)
    ));
}

#[test]
fn test_from_hex_str_small_values() {
    // Test single digit
    let result = U256::from_hex_str("0x1").unwrap();
    assert_eq!(result.low(), 1);
    assert_eq!(result.high(), 0);

    let result = U256::from_hex_str("0xf").unwrap();
    assert_eq!(result.low(), 15);
    assert_eq!(result.high(), 0);

    let result = U256::from_hex_str("0xF").unwrap();
    assert_eq!(result.low(), 15);
    assert_eq!(result.high(), 0);

    // Test without prefix
    let result = U256::from_hex_str("a").unwrap();
    assert_eq!(result.low(), 10);
    assert_eq!(result.high(), 0);

    let result = U256::from_hex_str("A").unwrap();
    assert_eq!(result.low(), 10);
    assert_eq!(result.high(), 0);
}

#[test]
fn test_from_hex_str_max_low_value() {
    // Test maximum u128 value (32 hex chars)
    let max_u128_hex = "ffffffffffffffffffffffffffffffff";
    let result = U256::from_hex_str(max_u128_hex).unwrap();
    assert_eq!(result.low(), u128::MAX);
    assert_eq!(result.high(), 0);

    // Test without prefix
    let max_u128_hex = "0xffffffffffffffffffffffffffffffff";
    let result = U256::from_hex_str(max_u128_hex).unwrap();
    assert_eq!(result.low(), u128::MAX);
    assert_eq!(result.high(), 0);
}

#[test]
fn test_from_hex_str_values_requiring_high() {
    // Test 33 hex chars (should use high part)
    let result = U256::from_hex_str("0x1ffffffffffffffffffffffffffffffff").unwrap();
    assert_eq!(result.low(), u128::MAX);
    assert_eq!(result.high(), 1);

    // Test with leading zeros that get trimmed
    let result =
        U256::from_hex_str("0x00000000000000000000000000000001ffffffffffffffffffffffffffffffff")
            .unwrap();
    assert_eq!(result.low(), u128::MAX);
    assert_eq!(result.high(), 1);

    // Test maximum value (64 hex chars)
    let max_hex = "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    let result = U256::from_hex_str(max_hex).unwrap();
    assert_eq!(result.low(), u128::MAX);
    assert_eq!(result.high(), u128::MAX);

    // Test maximum value (64 hex chars) with leading zeros
    let max_hex = "0x0000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    let result = U256::from_hex_str(max_hex).unwrap();
    assert_eq!(result.low(), u128::MAX);
    assert_eq!(result.high(), u128::MAX);

    // Test 64 chars (maximum allowed)
    let max_64 = "0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let result = U256::from_hex_str(max_64).unwrap();
    assert_eq!(
        result.high(),
        u128::from_str_radix("0123456789abcdef0123456789abcdef", 16).unwrap()
    );
    assert_eq!(
        result.low(),
        u128::from_str_radix("0123456789abcdef0123456789abcdef", 16).unwrap()
    );

    // Test a 40-character hex string to verify correct splitting
    let hex_40 = "0x1234567890abcdef1234567890abcdef12345678";
    let result = U256::from_hex_str(hex_40).unwrap();

    // Should split at position 8 (40 - 32 = 8)
    let expected_high = u128::from_str_radix("12345678", 16).unwrap();
    let expected_low = u128::from_str_radix("90abcdef1234567890abcdef12345678", 16).unwrap();

    assert_eq!(result.high(), expected_high);
    assert_eq!(result.low(), expected_low);
}

#[test]
fn test_from_hex_str_too_long() {
    // Test 65 hex chars (too big)
    let too_big = "0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    assert!(matches!(
        U256::from_hex_str(too_big),
        Err(FromStrError::StringTooLong)
    ));

    // Test without prefix
    let too_big = "1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    assert!(matches!(
        U256::from_hex_str(too_big),
        Err(FromStrError::StringTooLong)
    ));

    // Test even longer string
    let very_long = "1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111";
    assert!(matches!(
        U256::from_hex_str(very_long),
        Err(FromStrError::StringTooLong)
    ));
}

#[test]
fn test_from_hex_str_invalid_characters() {
    // Test invalid hex characters
    assert!(matches!(
        U256::from_hex_str("0xg"),
        Err(FromStrError::Parse(_))
    ));

    assert!(matches!(
        U256::from_hex_str("0x123g"),
        Err(FromStrError::Parse(_))
    ));

    assert!(matches!(
        U256::from_hex_str("0xz"),
        Err(FromStrError::Parse(_))
    ));

    // Test without prefix
    assert!(matches!(
        U256::from_hex_str("g"),
        Err(FromStrError::Parse(_))
    ));

    assert!(matches!(
        U256::from_hex_str("123g"),
        Err(FromStrError::Parse(_))
    ));

    // Test invalid characters in high part
    assert!(matches!(
        U256::from_hex_str("0xg123456789abcdef123456789abcdef12"),
        Err(FromStrError::Parse(_))
    ));

    // Test invalid characters in low part when high part is present
    assert!(matches!(
        U256::from_hex_str("0x1123456789abcdef123456789abcdefg2"),
        Err(FromStrError::Parse(_))
    ));
}

#[test]
fn test_from_hex_str_mixed_case() {
    // Test mixed case hex digits
    let result = U256::from_hex_str("0xaBcDeF123456789").unwrap();
    assert_eq!(
        result.low(),
        u128::from_str_radix("aBcDeF123456789", 16).unwrap()
    );
    assert_eq!(result.high(), 0);

    // Test mixed case in both parts
    let result = U256::from_hex_str("0xaBcDeF123456789aBcDeF123456789aBcDeF12").unwrap();
    assert_eq!(result.high(), u128::from_str_radix("aBcDeF", 16).unwrap());
    assert_eq!(
        result.low(),
        u128::from_str_radix("123456789aBcDeF123456789aBcDeF12", 16).unwrap()
    );
}

#[test]
fn test_from_hex_str_empty_string() {
    // Test empty string
    assert!(matches!(U256::from_hex_str(""), Err(FromStrError::Invalid)));
}
