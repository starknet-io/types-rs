use core::str::FromStr;

use crate::felt::{Felt, PrimitiveFromFeltError};

use super::U256;

mod from_dec_str;
mod from_hex_str;

#[test]
fn from_parts() {
    let value = U256::from_parts(0x2, 0x1);
    assert_eq!(value.low(), 0x1);
    assert_eq!(value.high(), 0x2);
    assert_eq!(value.low, 0x1);
    assert_eq!(value.high, 0x2);
}

#[test]
fn try_from_felt_parts() {
    let u128_max = Felt::from(u128::MAX);
    let u128_max_plus_one = u128_max + 1;

    assert!(U256::try_from_felt_parts(u128_max, u128_max).is_ok());
    assert!(matches!(
        U256::try_from_felt_parts(u128_max, u128_max_plus_one),
        Err(PrimitiveFromFeltError)
    ));
    assert!(matches!(
        U256::try_from_felt_parts(Felt::MAX, u128_max),
        Err(PrimitiveFromFeltError)
    ));
}

#[test]
fn try_from_dec_str_parts() {
    let valid_str = "123";
    assert!(U256::try_from_dec_str_parts(valid_str, valid_str).is_ok());
    let valid_str =
        "00000000000000000000000000000000000000000000000000000000000000000000000000000000000123";
    assert!(U256::try_from_dec_str_parts(valid_str, valid_str).is_ok());

    let invalid_str = "";
    assert!(U256::try_from_dec_str_parts(valid_str, invalid_str).is_err());
    let invalid_str = "10p";
    assert!(U256::try_from_dec_str_parts(invalid_str, valid_str).is_err());
    let invalid_str = "0x123";
    assert!(U256::try_from_dec_str_parts(invalid_str, valid_str).is_err());
}
#[test]
fn try_from_hex_str_parts() {
    let valid_str = "123";
    assert!(U256::try_from_hex_str_parts(valid_str, valid_str).is_ok());
    let valid_str = "0x123";
    assert!(U256::try_from_hex_str_parts(valid_str, valid_str).is_ok());
    let valid_str =
        "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000123";
    assert!(U256::try_from_hex_str_parts(valid_str, valid_str).is_ok());

    let invalid_str = "";
    assert!(U256::try_from_hex_str_parts(valid_str, invalid_str).is_err());
    let invalid_str = "10p";
    assert!(U256::try_from_hex_str_parts(invalid_str, valid_str).is_err());
    let invalid_str = "0x0x123";
    assert!(U256::try_from_hex_str_parts(invalid_str, valid_str).is_err());
}

#[test]
fn from_str() {
    let input = "0x1234";
    assert_eq!(
        U256::from_str(input).unwrap(),
        U256::from_hex_str(input).unwrap()
    );
    let input = "0X1234";
    assert_eq!(
        U256::from_str(input).unwrap(),
        U256::from_hex_str(input).unwrap()
    );
    let input = "1234";
    assert_eq!(
        U256::from_str(input).unwrap(),
        U256::from_dec_str(input).unwrap()
    );
    let input = "1234ff";
    assert!(U256::from_str(input).is_err());
    let input = "0x0x1";
    assert!(U256::from_str(input).is_err());
}

#[test]
fn ordering() {
    let value1 = U256::from_parts(2, 1);
    let value2 = U256::from_parts(1, 3);
    assert!(value2 < value1);
    assert_eq!(value2, value2);
}
