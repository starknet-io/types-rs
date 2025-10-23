use core::fmt;

use lambdaworks_math::{
    field::{
        element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
    },
    unsigned_integer::element::UnsignedInteger,
};

use crate::felt::Felt;

/// A non-zero [Felt].
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonZeroFelt(pub(crate) FieldElement<Stark252PrimeField>);

impl NonZeroFelt {
    /// Create a [NonZeroFelt] as a constant.
    /// # Safety
    /// If the value is zero will panic.
    pub const fn from_raw(value: [u64; 4]) -> Self {
        if value[0] == 0 && value[1] == 0 && value[2] == 0 && value[3] == 0 {
            panic!("Felt is zero");
        }
        let value = Felt::from_raw(value);
        Self(value.0)
    }

    /// [Felt] constant that's equal to 1.
    pub const ONE: Self = Self::from_felt_unchecked(Felt(
        FieldElement::<Stark252PrimeField>::from_hex_unchecked("1"),
    ));

    /// [Felt] constant that's equal to 2.
    pub const TWO: Self = Self::from_felt_unchecked(Felt(
        FieldElement::<Stark252PrimeField>::from_hex_unchecked("2"),
    ));

    /// [Felt] constant that's equal to 3.
    pub const THREE: Self = Self::from_felt_unchecked(Felt(
        FieldElement::<Stark252PrimeField>::from_hex_unchecked("3"),
    ));

    /// Maximum value of [Felt]. Equals to 2^251 + 17 * 2^192.
    pub const MAX: Self =
        Self::from_felt_unchecked(Felt(FieldElement::<Stark252PrimeField>::const_from_raw(
            UnsignedInteger::from_limbs([544, 0, 0, 32]),
        )));

    /// Create a [NonZeroFelt] without checking it. If the [Felt] is indeed [Felt::ZERO]
    /// this can lead to undefined behaviour and big security issue.
    /// You should always use the [TryFrom] implementation
    pub const fn from_felt_unchecked(value: Felt) -> Self {
        Self(value.0)
    }
}

#[derive(Debug)]
pub struct FeltIsZeroError;

#[cfg(feature = "std")]
impl std::error::Error for FeltIsZeroError {}

impl fmt::Display for FeltIsZeroError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "tried to create NonZeroFelt from 0".fmt(f)
    }
}

impl From<NonZeroFelt> for Felt {
    fn from(value: NonZeroFelt) -> Self {
        Self(value.0)
    }
}

impl From<&NonZeroFelt> for Felt {
    fn from(value: &NonZeroFelt) -> Self {
        Self(value.0)
    }
}

impl AsRef<NonZeroFelt> for NonZeroFelt {
    fn as_ref(&self) -> &NonZeroFelt {
        self
    }
}

impl TryFrom<Felt> for NonZeroFelt {
    type Error = FeltIsZeroError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        if value == Felt::ZERO {
            Err(FeltIsZeroError)
        } else {
            Ok(Self(value.0))
        }
    }
}

impl TryFrom<&Felt> for NonZeroFelt {
    type Error = FeltIsZeroError;

    fn try_from(value: &Felt) -> Result<Self, Self::Error> {
        if *value == Felt::ZERO {
            Err(FeltIsZeroError)
        } else {
            Ok(Self(value.0))
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    pub extern crate alloc;

    use proptest::prelude::*;

    use crate::felt::{Felt, NonZeroFelt, felt_arbitrary::nonzero_felt};

    #[test]
    fn nonzerofelt_from_raw() {
        let one_raw = [
            576460752303422960,
            18446744073709551615,
            18446744073709551615,
            18446744073709551585,
        ];
        assert_eq!(NonZeroFelt::from_raw(one_raw), NonZeroFelt::ONE);
        let two_raw = [
            576460752303422416,
            18446744073709551615,
            18446744073709551615,
            18446744073709551553,
        ];
        assert_eq!(NonZeroFelt::from_raw(two_raw), NonZeroFelt::TWO);
        let nineteen_raw = [
            576460752303413168,
            18446744073709551615,
            18446744073709551615,
            18446744073709551009,
        ];
        assert_eq!(
            NonZeroFelt::from_raw(nineteen_raw),
            NonZeroFelt::try_from(Felt::from(19)).unwrap()
        );
    }

    #[test]
    fn nonzerofelt_from_felt_unchecked() {
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unwrap("9028392")),
            NonZeroFelt::try_from(Felt::from(0x9028392)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unwrap("1")),
            NonZeroFelt::try_from(Felt::from(1)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unwrap("0x2")),
            NonZeroFelt::try_from(Felt::from(2)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unwrap("0x0000000003")),
            NonZeroFelt::try_from(Felt::from(3)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unwrap("000004")),
            NonZeroFelt::try_from(Felt::from(4)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unwrap("0x05b")),
            NonZeroFelt::try_from(Felt::from(91)).unwrap()
        );
        assert_eq!(
            NonZeroFelt::from_felt_unchecked(Felt::from_hex_unwrap("A")),
            NonZeroFelt::try_from(Felt::from(10)).unwrap()
        );
    }

    #[test]
    #[should_panic(expected = "Felt is zero")]
    fn nonzerofelt_is_zero_from_raw() {
        NonZeroFelt::from_raw([0; 4]);
    }

    #[test]
    fn non_zero_felt_from_zero_should_fail() {
        assert!(NonZeroFelt::try_from(Felt::ZERO).is_err());
    }

    proptest! {
        #[test]
        fn non_zero_felt_new_is_ok_when_not_zero(x in nonzero_felt()) {
            prop_assert!(NonZeroFelt::try_from(x).is_ok());
            prop_assert_eq!(NonZeroFelt::try_from(x).unwrap().0, x.0);
        }

        #[test]
        fn non_zero_is_not_zero(x in nonzero_felt()) {
            prop_assert!(x != Felt::ZERO)
        }

    }
}
