use core::fmt::Display;

use super::U256;

macro_rules! impl_from_uint {
    ($from:ty) => {
        impl From<$from> for U256 {
            fn from(value: $from) -> U256 {
                U256 {
                    high: 0,
                    low: value.into(),
                }
            }
        }
    };
}

impl_from_uint!(u8);
impl_from_uint!(u16);
impl_from_uint!(u32);
impl_from_uint!(u64);
impl_from_uint!(u128);

macro_rules! impl_try_from_int {
    ($from:ty) => {
        impl TryFrom<$from> for U256 {
            type Error = core::num::TryFromIntError;

            fn try_from(value: $from) -> Result<Self, Self::Error> {
                Ok(U256 {
                    high: 0,
                    low: value.try_into()?,
                })
            }
        }
    };
}

impl_try_from_int!(i8);
impl_try_from_int!(i16);
impl_try_from_int!(i32);
impl_try_from_int!(i64);
impl_try_from_int!(i128);

#[derive(Debug)]
pub struct TryFromU256Error;

impl Display for TryFromU256Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        "out of range u256 type conversion attempted".fmt(f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryFromU256Error {}

macro_rules! impl_try_from_u256 {
    ($to:ty) => {
        impl TryFrom<U256> for $to {
            type Error = TryFromU256Error;

            fn try_from(value: U256) -> Result<Self, Self::Error> {
                if value.high != 0 {
                    Err(TryFromU256Error)
                } else {
                    value.low.try_into().map_err(|_| TryFromU256Error)
                }
            }
        }
    };
}

impl_try_from_u256!(u8);
impl_try_from_u256!(u16);
impl_try_from_u256!(u32);
impl_try_from_u256!(u64);
impl_try_from_u256!(u128);
impl_try_from_u256!(i8);
impl_try_from_u256!(i16);
impl_try_from_u256!(i32);
impl_try_from_u256!(i64);
impl_try_from_u256!(i128);
