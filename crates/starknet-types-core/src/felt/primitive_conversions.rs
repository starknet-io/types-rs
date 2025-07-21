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
                // We'll split the conversion in 3 case:
                // Felt >= 0
                // Felt < -1
                // Felt == -1

                // Get the size of the type we'll convert the felt into
                let size_of_type = core::mem::size_of::<$into>();
                // Convert the felt as little endian bytes
                let bytes_le = value.to_bytes_le();

                // Case 1: Felt >= 0
                // Our felt type can hold values up to roughly 2**252 bits which is encoded in 32 bytes.
                // The type we'll convert the value into can hold `size_of_type` (= { 1, 2, 4, 8, 16 }) bytes.
                // If all the bytes after the last byte that our target type can fit are 0 it means that the
                // number is positive.
                // The target type is a signed type which means that the leftmost bit of the last byte
                // (remember we're in little endian) is used for the sign (0 for positive numbers)
                // so the last byte can hold a value up to 0b01111111
                if bytes_le[size_of_type..].iter().all(|&v| v == 0)
                    && bytes_le[size_of_type - 1] <= 0b01111111
                {
                    Ok(<$into>::from_le_bytes(
                        bytes_le[..size_of_type].try_into().unwrap(),
                    ))
                }
                // Case 2: Felt < -1
                // Similarly to how we checked that the number was positive by checking the bytes after the
                // `size_of_type` byte we check that all the bytes after correspond to the bytes of a negative felt
                // The leftmost bit is use for the sign, as it's a negative number it has to be 1.
                else if bytes_le[size_of_type..] == MINUS_TWO_BYTES_REPR[size_of_type..]
                    && bytes_le[size_of_type - 1] >= 0b10000000
                {
                    // We take the `size_of_type` first bytes because they contain the useful value.
                    let offsetted_value =
                        <$into>::from_le_bytes(bytes_le[..size_of_type].try_into().unwrap());

                    // Quite conveniently the byte representation of the `size_of` least significant bytes
                    // is the one of the negative value we are looking for +1.
                    // So we just have to remove 1 to get the actual value.
                    offsetted_value.checked_sub(1).ok_or(PrimitiveFromFeltError)
                // Case 3: Felt == -1
                // This is the little endian representation of Felt::MAX. And Felt::MAX is exactly -1
                // [
                //    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                //    0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 8,
                // ]
                // The only valid Felt with those most significant bytes is Felt::MAX.
                // All other arrays with those most significant bytes are invalid Felts because they would be >= Prime.
                } else if bytes_le[24..] == [17, 0, 0, 0, 0, 0, 0, 8] {
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
        assert_eq!(
            u8_max_value,
            u8::try_from(Felt::from(u8_max_value)).unwrap()
        );
        let u8_42_value = 42u8;
        assert_eq!(u8_42_value, u8::try_from(Felt::from(u8_42_value)).unwrap());
        let u8_zero_value = 0u8;
        assert_eq!(
            u8_zero_value,
            u8::try_from(Felt::from(u8_zero_value)).unwrap()
        );
        // u16
        let u16_max_value = u16::MAX;
        assert_eq!(
            u16_max_value,
            u16::try_from(Felt::from(u16_max_value)).unwrap()
        );
        let u16_42_value = 42u16;
        assert_eq!(
            u16_42_value,
            u16::try_from(Felt::from(u16_42_value)).unwrap()
        );
        let u16_zero_value = 0u16;
        assert_eq!(
            u16_zero_value,
            u16::try_from(Felt::from(u16_zero_value)).unwrap()
        );
        // u32
        let u32_max_value = u32::MAX;
        assert_eq!(
            u32_max_value,
            u32::try_from(Felt::from(u32_max_value)).unwrap()
        );
        let u32_42_value = 42u32;
        assert_eq!(
            u32_42_value,
            u32::try_from(Felt::from(u32_42_value)).unwrap()
        );
        let u32_zero_value = 0u32;
        assert_eq!(
            u32_zero_value,
            u32::try_from(Felt::from(u32_zero_value)).unwrap()
        );
        // u64
        let u64_max_value = u64::MAX;
        assert_eq!(
            u64_max_value,
            u64::try_from(Felt::from(u64_max_value)).unwrap()
        );
        let u64_42_value = 42u64;
        assert_eq!(
            u64_42_value,
            u64::try_from(Felt::from(u64_42_value)).unwrap()
        );
        let u64_zero_value = 0u64;
        assert_eq!(
            u64_zero_value,
            u64::try_from(Felt::from(u64_zero_value)).unwrap()
        );
        // u128
        let u128_max_value = u128::MAX;
        assert_eq!(
            u128_max_value,
            u128::try_from(Felt::from(u128_max_value)).unwrap()
        );
        let u128_42_value = 42u128;
        assert_eq!(
            u128_42_value,
            u128::try_from(Felt::from(u128_42_value)).unwrap()
        );
        let u128_zero_value = 0u128;
        assert_eq!(
            u128_zero_value,
            u128::try_from(Felt::from(u128_zero_value)).unwrap()
        );
        // usize
        let usize_max_value = usize::MAX;
        assert_eq!(
            usize_max_value,
            usize::try_from(Felt::from(usize_max_value)).unwrap()
        );
        let usize_42_value = 42usize;
        assert_eq!(
            usize_42_value,
            usize::try_from(Felt::from(usize_42_value)).unwrap()
        );
        let usize_zero_value = 0usize;
        assert_eq!(
            usize_zero_value,
            usize::try_from(Felt::from(usize_zero_value)).unwrap()
        );
    }

    #[test]
    fn from_and_try_from_works_both_way_for_all_valid_i8_and_i16_values() {
        // i8
        for i in i8::MIN..i8::MAX {
            assert_eq!(i, i8::try_from(Felt::from(i)).unwrap());
        }
        // i16
        for i in i16::MIN..i16::MAX {
            assert_eq!(i, i16::try_from(Felt::from(i)).unwrap());
        }
        // For the others types it would be too long to test every value exhaustively,
        // so we only check keys values in `from_and_try_from_works_both_way_for_valid_signed_values`
    }

    #[test]
    fn from_and_try_from_works_both_way_for_valid_signed_values() {
        // i32
        let i32_max = i32::MAX;
        assert_eq!(i32_max, i32::try_from(Felt::from(i32_max)).unwrap());
        let i32_min = i32::MIN;
        assert_eq!(i32_min, i32::try_from(Felt::from(i32_min)).unwrap());
        let i32_zero = 0i32;
        assert_eq!(i32_zero, i32::try_from(Felt::from(i32_zero)).unwrap());
        let i32_minus_one = -1i32;
        assert_eq!(
            i32_minus_one,
            i32::try_from(Felt::from(i32_minus_one)).unwrap()
        );
        // i64
        let i64_max = i64::MAX;
        assert_eq!(i64_max, i64::try_from(Felt::from(i64_max)).unwrap());
        let i64_min = i64::MIN;
        assert_eq!(i64_min, i64::try_from(Felt::from(i64_min)).unwrap());
        let i64_zero = 0i64;
        assert_eq!(i64_zero, i64::try_from(Felt::from(i64_zero)).unwrap());
        let i64_minus_one = -1i64;
        assert_eq!(
            i64_minus_one,
            i64::try_from(Felt::from(i64_minus_one)).unwrap()
        );
        // isize
        let isize_max = isize::MAX;
        assert_eq!(isize_max, isize::try_from(Felt::from(isize_max)).unwrap());
        let isize_min = isize::MIN;
        assert_eq!(isize_min, isize::try_from(Felt::from(isize_min)).unwrap());
        let isize_zero = 0isize;
        assert_eq!(isize_zero, isize::try_from(Felt::from(isize_zero)).unwrap());
        let isize_minus_one = -1isize;
        assert_eq!(
            isize_minus_one,
            isize::try_from(Felt::from(isize_minus_one)).unwrap()
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
        for i in (i8::MAX as i16 + 1)..i16::MAX {
            let f = Felt::from(i);
            assert!(i8::try_from(f).is_err());
        }
        for i in i16::MIN..(i8::MIN as i16 - 1) {
            let f = Felt::from(i);
            assert!(i8::try_from(f).is_err());
        }
        // It would be too expansive to check all values of larger types,
        // so we just check some key ones

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
        let under_i128_min = Felt::from(i128::MIN) - 2;
        assert!(i8::try_from(under_i128_min).is_err());
        assert!(i16::try_from(under_i128_min).is_err());
        assert!(i32::try_from(under_i128_min).is_err());
        assert!(i64::try_from(under_i128_min).is_err());
        assert!(isize::try_from(under_i128_min).is_err());
        assert!(i128::try_from(under_i128_min).is_err());
    }

    #[test]
    fn felt_from_into_bool() {
        assert!(Felt::from(true) == Felt::ONE);
        assert!(Felt::from(false) == Felt::ZERO);
    }
}
