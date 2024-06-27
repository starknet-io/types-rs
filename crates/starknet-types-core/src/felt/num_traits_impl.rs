use super::Felt;
use num_bigint::{ToBigInt, ToBigUint};
use num_traits::{FromPrimitive, Inv, One, Pow, ToPrimitive, Zero};

impl ToBigInt for Felt {
    /// Converts the value of `self` to a [`BigInt`].
    ///
    /// Safe to unwrap, will always return `Some`.
    fn to_bigint(&self) -> Option<num_bigint::BigInt> {
        Some(self.to_bigint())
    }
}

impl ToBigUint for Felt {
    /// Converts the value of `self` to a [`BigUint`].
    ///
    /// Safe to unwrap, will always return `Some`.
    fn to_biguint(&self) -> Option<num_bigint::BigUint> {
        Some(self.to_biguint())
    }
}

impl FromPrimitive for Felt {
    fn from_i64(value: i64) -> Option<Self> {
        Some(value.into())
    }

    fn from_u64(value: u64) -> Option<Self> {
        Some(value.into())
    }

    fn from_i128(value: i128) -> Option<Self> {
        Some(value.into())
    }

    fn from_u128(value: u128) -> Option<Self> {
        Some(value.into())
    }
}

// TODO: we need to decide whether we want conversions to signed primitives
// will support converting the high end of the field to negative.
impl ToPrimitive for Felt {
    fn to_u64(&self) -> Option<u64> {
        self.to_u128().and_then(|x| u64::try_from(x).ok())
    }

    fn to_i64(&self) -> Option<i64> {
        self.to_u128().and_then(|x| i64::try_from(x).ok())
    }

    fn to_u128(&self) -> Option<u128> {
        match self.0.representative().limbs {
            [0, 0, hi, lo] => Some((lo as u128) | ((hi as u128) << 64)),
            _ => None,
        }
    }

    fn to_i128(&self) -> Option<i128> {
        self.to_u128().and_then(|x| i128::try_from(x).ok())
    }
}

impl Zero for Felt {
    fn is_zero(&self) -> bool {
        *self == Felt::ZERO
    }

    fn zero() -> Felt {
        Felt::ZERO
    }
}

impl One for Felt {
    fn one() -> Self {
        Felt::ONE
    }
}

impl Inv for Felt {
    type Output = Option<Self>;

    fn inv(self) -> Self::Output {
        self.inverse()
    }
}

impl Pow<u8> for Felt {
    type Output = Self;

    fn pow(self, rhs: u8) -> Self::Output {
        Self(self.0.pow(rhs as u128))
    }
}
impl Pow<u16> for Felt {
    type Output = Self;

    fn pow(self, rhs: u16) -> Self::Output {
        Self(self.0.pow(rhs as u128))
    }
}
impl Pow<u32> for Felt {
    type Output = Self;

    fn pow(self, rhs: u32) -> Self::Output {
        Self(self.0.pow(rhs as u128))
    }
}
impl Pow<u64> for Felt {
    type Output = Self;

    fn pow(self, rhs: u64) -> Self::Output {
        Self(self.0.pow(rhs as u128))
    }
}
impl Pow<u128> for Felt {
    type Output = Self;

    fn pow(self, rhs: u128) -> Self::Output {
        Self(self.0.pow(rhs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_is_zero() {
        assert!(Felt::ZERO.is_zero());
    }

    #[test]
    fn one_is_one() {
        assert!(Felt::ONE.is_one());
    }

    #[test]
    fn default_is_zero() {
        assert!(Felt::default().is_zero());
    }
}
