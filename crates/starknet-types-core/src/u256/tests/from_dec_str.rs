use crate::u256::{FromStrError, U256};

#[test]
fn test_from_dec_str_zero_values() {
    // Test "0"
    let result = U256::from_dec_str("0").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);

    // Test multiple zeros
    let result = U256::from_dec_str("000").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);

    let result = U256::from_dec_str("0000000000000000000000000000000000000000").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);
}

#[test]
fn test_from_dec_str_invalid_empty_after_trimming() {
    // Test empty string
    assert!(matches!(U256::from_dec_str(""), Err(FromStrError::Invalid)));
}

#[test]
fn test_from_dec_str_small_values() {
    // Test single digit
    let result = U256::from_dec_str("1").unwrap();
    assert_eq!(result.low(), 1);
    assert_eq!(result.high(), 0);

    let result = U256::from_dec_str("9").unwrap();
    assert_eq!(result.low(), 9);
    assert_eq!(result.high(), 0);

    // Test multiple digits
    let result = U256::from_dec_str("123").unwrap();
    assert_eq!(result.low(), 123);
    assert_eq!(result.high(), 0);

    let result = U256::from_dec_str("999").unwrap();
    assert_eq!(result.low(), 999);
    assert_eq!(result.high(), 0);
}

#[test]
fn test_from_dec_str_max_u128_value() {
    let max_u128_str = "340282366920938463463374607431768211455";
    let result = U256::from_dec_str(max_u128_str).unwrap();
    assert_eq!(result.low(), u128::MAX);
    assert_eq!(result.high(), 0);

    let max_u128_plus_one_str = "340282366920938463463374607431768211456";
    let result = U256::from_dec_str(max_u128_plus_one_str).unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 1);

    let max_u128_plus_two_str = "340282366920938463463374607431768211457";
    let result = U256::from_dec_str(max_u128_plus_two_str).unwrap();
    assert_eq!(result.low(), 1);
    assert_eq!(result.high(), 1);
}

#[test]
fn test_from_dec_str_values_under_39_digits() {
    // Test values with less than 39 digits (should only use low part)
    let result = U256::from_dec_str("12345678901234567890123456789012345678").unwrap(); // 38 digits
    assert_eq!(result.low(), 12345678901234567890123456789012345678u128);
    assert_eq!(result.high(), 0);

    // Test a smaller value
    let result = U256::from_dec_str("1000000000000000000000000000000000000").unwrap(); // 37 digits
    assert_eq!(result.low(), 1000000000000000000000000000000000000u128);
    assert_eq!(result.high(), 0);
}

#[test]
fn test_from_dec_str_values_39_digits_and_above() {
    // Test 39 digits (should use manual parsing)
    let result = U256::from_dec_str("123456789012345678901234567890123456789").unwrap(); // 39 digits
    // This should use the manual parsing logic
    assert!(result.low() > 0 || result.high() > 0);

    // Test a specific known value that exceeds u128::MAX
    let result = U256::from_dec_str("340282366920938463463374607431768211456").unwrap(); // u128::MAX + 1
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 1);
}

#[test]
fn test_from_dec_str_maximum_allowed_value() {
    // Test maximum value for u256 (78 digits)
    let max_u256_str =
        "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    let result = U256::from_dec_str(max_u256_str).unwrap();
    assert_eq!(result.low(), u128::MAX);
    assert_eq!(result.high(), u128::MAX);

    let max_u256_plus_one_str =
        "115792089237316195423570985008687907853269984665640564039457584007913129639936";
    assert!(matches!(
        U256::from_dec_str(max_u256_plus_one_str),
        Err(FromStrError::ValueTooBig)
    ));
}

#[test]
fn test_from_dec_str_too_long() {
    // Test 79 digits (too big)
    let too_big = "1157920892373161954235709850086879078532699846656405640394575840079131296399350";
    assert!(matches!(
        U256::from_dec_str(too_big),
        Err(FromStrError::StringTooLong)
    ));

    // Test even longer string
    let very_long = "1".repeat(100);
    assert!(matches!(
        U256::from_dec_str(&very_long),
        Err(FromStrError::StringTooLong)
    ));
}

#[test]
fn test_from_dec_str_invalid_characters_lower_only() {
    // Test invalid decimal characters
    assert!(matches!(
        U256::from_dec_str("123a"),
        Err(FromStrError::Invalid)
    ));

    assert!(matches!(
        U256::from_dec_str("12.3"),
        Err(FromStrError::Invalid)
    ));

    assert!(matches!(
        U256::from_dec_str("12-3"),
        Err(FromStrError::Invalid)
    ));

    assert!(matches!(
        U256::from_dec_str("12+3"),
        Err(FromStrError::Invalid)
    ));

    assert!(matches!(
        U256::from_dec_str("12 3"),
        Err(FromStrError::Invalid)
    ));

    // Test characters outside 0-9 range
    assert!(matches!(
        U256::from_dec_str("12:3"), // ':' is ASCII 58, '0' is 48, so b':' - b'0' = 10
        Err(FromStrError::Invalid)
    ));

    assert!(matches!(
        U256::from_dec_str("12/3"), // '/' is ASCII 47, '0' is 48, so b'/' - b'0' = 255 (wrapping)
        Err(FromStrError::Invalid)
    ));
}

#[test]
fn test_from_dec_str_leading_zeros() {
    // Test leading zeros that should be trimmed
    let result =
        U256::from_dec_str("0000000000000000000000000000000000000000000000000000000000000001")
            .unwrap();
    assert_eq!(result.low(), 1);
    assert_eq!(result.high(), 0);

    let result =
        U256::from_dec_str("00000000000000000000000000000000000000000000000000000000000000123")
            .unwrap();
    assert_eq!(result.low(), 123);
    assert_eq!(result.high(), 0);

    // Test case where all characters are zeros
    let result = U256::from_dec_str("00000000000000000000000000000000").unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 0);
}

#[test]
fn test_from_dec_str_boundary_lengths() {
    // Test exactly 78 digits (maximum allowed)
    let max_78 = "111456789012345678901234567890123456789012345678901234567890123456789012345678";
    let result = U256::from_dec_str(max_78).unwrap();
    assert!(result.low() > 0 || result.high() > 0);

    // Test exactly 38 digits (just under 39)
    let digits_38 = "340282366920938463463374607431768211455";
    let result = U256::from_dec_str(digits_38).unwrap();
    assert_eq!(result.low(), 340282366920938463463374607431768211455u128);
    assert_eq!(result.high(), 0);

    // Test exactly 39 digits (boundary for manual parsing)
    let digits_39 = "123456789012345678901234567890123456789";
    let result = U256::from_dec_str(digits_39).unwrap();
    assert!(result.low() > 0 || result.high() > 0);
}

#[test]
fn test_from_dec_str_overflow_detection() {
    // Test values that would cause overflow during manual parsing
    // This tests the overflow detection in the multiplication and addition steps

    // Test a value that's close to but not exceeding the limit
    let near_max = "115792089237316195423570985008687907853269984665640564039457584007913129639934";
    let result = U256::from_dec_str(near_max).unwrap();
    assert!(result.low() > 0 || result.high() > 0);

    // Test a value that would exceed u256 during intermediate calculations
    let overflow_test =
        "999999999999999999999999999999999999999999999999999999999999999999999999999999";
    let x = U256::from_dec_str(overflow_test);
    assert!(matches!(x, Err(FromStrError::ValueTooBig)));
}

#[test]
fn test_from_dec_str_specific_known_values() {
    // Test some specific known values to verify correctness

    // Test 10^38 (should use manual parsing)
    let ten_to_38 = "100000000000000000000000000000000000000"; // 1 followed by 38 zeros
    let result = U256::from_dec_str(ten_to_38).unwrap();
    assert!(result.low() > 0 || result.high() > 0);

    // Test 2^128 (should be high=1, low=0)
    let two_to_128 = "340282366920938463463374607431768211456"; // 2^128
    let result = U256::from_dec_str(two_to_128).unwrap();
    assert_eq!(result.low(), 0);
    assert_eq!(result.high(), 1);

    // Test 2^64
    let two_to_64 = "18446744073709551616"; // 2^64
    let result = U256::from_dec_str(two_to_64).unwrap();
    assert_eq!(result.low(), 18446744073709551616u128);
    assert_eq!(result.high(), 0);
}

#[test]
fn test_from_dec_str_parse_error_for_small_values() {
    // Test that invalid characters in small values (< 39 digits) return Parse error
    assert!(matches!(
        U256::from_dec_str("1234567890123456789012a"),
        Err(FromStrError::Invalid)
    ));

    assert!(matches!(
        U256::from_dec_str("1234567890123456789012.8"),
        Err(FromStrError::Invalid)
    ));
}

#[test]
fn test_from_dec_str_parse_error_for_big_values() {
    // Test that invalid characters in small values (< 39 digits) return Parse error
    assert!(matches!(
        U256::from_dec_str(
            "11579208923731619542357098500868790785326998466564056403945758400791312963993a"
        ),
        Err(FromStrError::Invalid)
    ));

    assert!(matches!(
        U256::from_dec_str(
            "11579208923731619542357098500868790785326998466564056403945758400791312963993 "
        ),
        Err(FromStrError::Invalid)
    ));
}
