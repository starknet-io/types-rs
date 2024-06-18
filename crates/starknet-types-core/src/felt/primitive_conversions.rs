use lambdaworks_math::{field::element::FieldElement, unsigned_integer::element::UnsignedInteger};

use super::Felt;

// Bool <-> Felt

impl From<bool> for Felt {
    fn from(value: bool) -> Felt {
        match value {
            true => Felt::ONE,
            false => Felt::ZERO,
        }
    }
}

impl From<Felt> for bool {
    fn from(value: Felt) -> Self {
        value != Felt::ZERO
    }
}

// From<primitive> for Felt

macro_rules! impl_from {
    ($from:ty, $with:ty) => {
        impl From<$from> for Felt {
            fn from(value: $from) -> Self {
                (value as $with).into()
            }
        }
    };
}

impl_from!(u8, u128);
impl_from!(u16, u128);
impl_from!(u32, u128);
impl_from!(u64, u128);
impl_from!(usize, u128);
impl_from!(i8, i128);
impl_from!(i16, i128);
impl_from!(i32, i128);
impl_from!(i64, i128);
impl_from!(isize, i128);

impl From<u128> for Felt {
    fn from(value: u128) -> Felt {
        Self(FieldElement::from(&UnsignedInteger::from(value)))
    }
}

impl From<i128> for Felt {
    fn from(value: i128) -> Felt {
        let mut res = Self(FieldElement::from(&UnsignedInteger::from(
            value.unsigned_abs(),
        )));
        if value.is_negative() {
            res = -res;
        }
        res
    }
}

// TryFrom<Felt> for primitive

#[derive(Debug, Copy, Clone)]
pub struct PrimitiveFromFeltError;

#[cfg(feature = "std")]
impl std::error::Error for PrimitiveFromFeltError {}

impl core::fmt::Display for PrimitiveFromFeltError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Failed to convert `Felt` into primitive type")
    }
}

macro_rules! impl_try_felt_into_unsigned {
    ($into: ty) => {
        impl TryFrom<Felt> for $into {
            type Error = PrimitiveFromFeltError;

            fn try_from(value: Felt) -> Result<$into, Self::Error> {
                let bytes_be = value.to_bytes_le();
                let (bytes_to_return, bytes_to_check) =
                    bytes_be.split_at(core::mem::size_of::<$into>());

                if bytes_to_check.iter().all(|&v| v == 0) {
                    Ok(<$into>::from_le_bytes(bytes_to_return.try_into().unwrap()))
                } else {
                    Err(PrimitiveFromFeltError)
                }
            }
        }
    };
}

impl_try_felt_into_unsigned!(u8);
impl_try_felt_into_unsigned!(u16);
impl_try_felt_into_unsigned!(u32);
impl_try_felt_into_unsigned!(u64);
impl_try_felt_into_unsigned!(usize);
impl_try_felt_into_unsigned!(u128);

const MINUS_TWO_BYTES_REPR: [u8; 32] = [
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 16, 0, 0, 0, 0, 0, 0, 8,
];

macro_rules! impl_try_felt_into_signed {
    ($into: ty) => {
        impl TryFrom<Felt> for $into {
            type Error = PrimitiveFromFeltError;

            // Let's call `s` the `size_of_type`.
            //
            // There is 3 ways the value we are looking for can be encoded in the Felt bytes:
            // 1. Positive numbers:
            //  Bytes [s..] are all set to zero, and byte [s] value must not exceed 127
            // 2. Negative numbers:
            //  Bytes [s..] should match `MINUS_TWO_BYTES_REPR`, and byte [s] value must not be less than 128
            // 3. -1:
            //  Bytes are those of Felt::MAX
            fn try_from(value: Felt) -> Result<Self, Self::Error> {
                let size_of_type = core::mem::size_of::<$into>();
                let bytes_be = value.to_bytes_le();

                // Positive numbers
                if bytes_be[size_of_type..].iter().all(|&v| v == 0)
                    && bytes_be[size_of_type - 1] <= 0x7f
                {
                    Ok(<$into>::from_le_bytes(
                        bytes_be[..size_of_type].try_into().unwrap(),
                    ))
                }
                // Negative numbers
                else if bytes_be[size_of_type..] == MINUS_TWO_BYTES_REPR[size_of_type..]
                    && bytes_be[size_of_type - 1] >= 80
                {
                    let offsetted_value =
                        <$into>::from_le_bytes(bytes_be[..size_of_type].try_into().unwrap());

                    // Quite conveniently the byte representation of the `s` least significant bytes
                    // is the one of the negative value we are looking for +1.
                    offsetted_value.checked_sub(1).ok_or(PrimitiveFromFeltError)
                // -1
                } else if bytes_be[24..] == [17, 0, 0, 0, 0, 0, 0, 8] {
                    // The only valid Felt with those most significant bytes is Felt::MAX.
                    // All other arrays with those most significant bytes are invalid Felts.
                    return Ok(-1);
                } else {
                    Err(PrimitiveFromFeltError)
                }
            }
        }
    };
}

impl_try_felt_into_signed!(i8);
impl_try_felt_into_signed!(i16);
impl_try_felt_into_signed!(i32);
impl_try_felt_into_signed!(i64);
impl_try_felt_into_signed!(isize);
impl_try_felt_into_signed!(i128);

#[cfg(test)]
mod tests {
    use crate::felt::Felt;

    #[test]
    fn from_and_try_from_works_both_way_for_valid_unsigned_values() {
        // u8
        let u8_max_value = u8::MAX;
        assert_eq!(u8_max_value, Felt::from(u8_max_value).try_into().unwrap());
        let u8_42_value = 42u8;
        assert_eq!(u8_42_value, Felt::from(u8_42_value).try_into().unwrap());
        let u8_zero_value = 0u8;
        assert_eq!(u8_zero_value, Felt::from(u8_zero_value).try_into().unwrap());
        // u16
        let u16_max_value = u16::MAX;
        assert_eq!(u16_max_value, Felt::from(u16_max_value).try_into().unwrap());
        let u16_42_value = 42u16;
        assert_eq!(u16_42_value, Felt::from(u16_42_value).try_into().unwrap());
        let u16_zero_value = 0u16;
        assert_eq!(
            u16_zero_value,
            Felt::from(u16_zero_value).try_into().unwrap()
        );
        // u32
        let u32_max_value = u32::MAX;
        assert_eq!(u32_max_value, Felt::from(u32_max_value).try_into().unwrap());
        let u32_42_value = 42u32;
        assert_eq!(u32_42_value, Felt::from(u32_42_value).try_into().unwrap());
        let u32_zero_value = 0u32;
        assert_eq!(
            u32_zero_value,
            Felt::from(u32_zero_value).try_into().unwrap()
        );
        // u64
        let u64_max_value = u64::MAX;
        assert_eq!(u64_max_value, Felt::from(u64_max_value).try_into().unwrap());
        let u64_42_value = 42u64;
        assert_eq!(u64_42_value, Felt::from(u64_42_value).try_into().unwrap());
        let u64_zero_value = 0u64;
        assert_eq!(
            u64_zero_value,
            Felt::from(u64_zero_value).try_into().unwrap()
        );
        // u128
        let u128_max_value = u128::MAX;
        assert_eq!(
            u128_max_value,
            Felt::from(u128_max_value).try_into().unwrap()
        );
        let u128_42_value = 42u128;
        assert_eq!(u128_42_value, Felt::from(u128_42_value).try_into().unwrap());
        let u128_zero_value = 0u128;
        assert_eq!(
            u128_zero_value,
            Felt::from(u128_zero_value).try_into().unwrap()
        );
        // usize
        let usize_max_value = usize::MAX;
        assert_eq!(
            usize_max_value,
            Felt::from(usize_max_value).try_into().unwrap()
        );
        let usize_42_value = 42usize;
        assert_eq!(
            usize_42_value,
            Felt::from(usize_42_value).try_into().unwrap()
        );
        let usize_zero_value = 0usize;
        assert_eq!(
            usize_zero_value,
            Felt::from(usize_zero_value).try_into().unwrap()
        );
    }

    #[test]
    fn from_and_try_from_works_both_way_for_valid_signed_values() {
        // i8
        let i8_max = i8::MAX;
        assert_eq!(i8_max, Felt::from(i8_max).try_into().unwrap());
        let i8_min = i8::MIN;
        assert_eq!(i8_min, Felt::from(i8_min).try_into().unwrap());
        let i8_zero = 0i8;
        assert_eq!(i8_zero, Felt::from(i8_zero).try_into().unwrap());
        let i8_minus_one = -1i8;
        assert_eq!(i8_minus_one, Felt::from(i8_minus_one).try_into().unwrap());
        // i16
        let i16_max = i16::MAX;
        assert_eq!(i16_max, Felt::from(i16_max).try_into().unwrap());
        let i16_min = i16::MIN;
        assert_eq!(i16_min, Felt::from(i16_min).try_into().unwrap());
        let i16_zero = 0i16;
        assert_eq!(i16_zero, Felt::from(i16_zero).try_into().unwrap());
        let i16_minus_one = -1i16;
        assert_eq!(i16_minus_one, Felt::from(i16_minus_one).try_into().unwrap());
        // i32
        let i32_max = i32::MAX;
        assert_eq!(i32_max, Felt::from(i32_max).try_into().unwrap());
        let i32_min = i32::MIN;
        assert_eq!(i32_min, Felt::from(i32_min).try_into().unwrap());
        let i32_zero = 0i32;
        assert_eq!(i32_zero, Felt::from(i32_zero).try_into().unwrap());
        let i32_minus_one = -1i32;
        assert_eq!(i32_minus_one, Felt::from(i32_minus_one).try_into().unwrap());
        // i64
        let i64_max = i64::MAX;
        assert_eq!(i64_max, Felt::from(i64_max).try_into().unwrap());
        let i64_min = i64::MIN;
        assert_eq!(i64_min, Felt::from(i64_min).try_into().unwrap());
        let i64_zero = 0i64;
        assert_eq!(i64_zero, Felt::from(i64_zero).try_into().unwrap());
        let i64_minus_one = -1i64;
        assert_eq!(i64_minus_one, Felt::from(i64_minus_one).try_into().unwrap());
        // isize
        let isize_max = isize::MAX;
        assert_eq!(isize_max, Felt::from(isize_max).try_into().unwrap());
        let isize_min = isize::MIN;
        assert_eq!(isize_min, Felt::from(isize_min).try_into().unwrap());
        let isize_zero = 0isize;
        assert_eq!(isize_zero, Felt::from(isize_zero).try_into().unwrap());
        let isize_minus_one = -1isize;
        assert_eq!(
            isize_minus_one,
            Felt::from(isize_minus_one).try_into().unwrap()
        );
        // i128
        let i128_max = i128::MAX;
        assert_eq!(i128_max, Felt::from(i128_max).try_into().unwrap());
        let i128_min = i128::MIN;
        assert_eq!(i128_min, Felt::from(i128_min).try_into().unwrap());
        let i128_zero = 0i128;
        assert_eq!(i128_zero, Felt::from(i128_zero).try_into().unwrap());
        let i128_minus_one = -1i128;
        assert_eq!(
            i128_minus_one,
            Felt::from(i128_minus_one).try_into().unwrap()
        );
    }

    #[test]
    fn try_from_fail_for_out_of_boud_values() {
        let over_i128_max = Felt::from(i128::MAX) + 1;
        assert!(i8::try_from(over_i128_max).is_err());
        assert!(i16::try_from(over_i128_max).is_err());
        assert!(i32::try_from(over_i128_max).is_err());
        assert!(i64::try_from(over_i128_max).is_err());
        assert!(isize::try_from(over_i128_max).is_err());
        assert!(i128::try_from(over_i128_max).is_err());

        let under_i128_min = Felt::from(i128::MIN) - 1;
        assert!(i8::try_from(under_i128_min).is_err());
        assert!(i16::try_from(under_i128_min).is_err());
        assert!(i32::try_from(under_i128_min).is_err());
        assert!(i64::try_from(under_i128_min).is_err());
        assert!(isize::try_from(under_i128_min).is_err());
        assert!(i128::try_from(under_i128_min).is_err());
    }

    #[test]
    fn felt_from_into_bool() {
        assert!(bool::from(Felt::from(true)));
        assert!(!bool::from(Felt::from(false)));

        assert!(bool::from(Felt::MAX));
        assert!(!bool::from(Felt::ZERO));
    }
}
