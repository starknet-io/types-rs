use super::Felt;
use num_bigint::{ToBigInt, ToBigUint};
use num_traits::{
    CheckedAdd, CheckedMul, CheckedSub, FromPrimitive, Inv, One, Pow, ToPrimitive, Zero,
};

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

impl CheckedAdd for Felt {
    fn checked_add(&self, v: &Self) -> Option<Self> {
        let res = self + v;
        if res < *self {
            None
        } else {
            Some(res)
        }
    }
}

impl CheckedMul for Felt {
    fn checked_mul(&self, v: &Self) -> Option<Self> {
        let (min, max) = if self < v { (self, v) } else { (v, self) };

        if *min == Felt::ZERO {
            return Some(*min);
        }

        let res = self * v;
        if res < *max {
            None
        } else {
            Some(res)
        }
    }
}

impl CheckedSub for Felt {
    fn checked_sub(&self, v: &Self) -> Option<Self> {
        let res = self - v;
        if res > *self {
            None
        } else {
            Some(res)
        }
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

    #[test]
    fn checked_ops() {
        // Add
        assert_eq!(Felt::ONE.checked_add(&Felt::TWO), Some(Felt::THREE));
        assert_eq!(Felt::ONE.checked_add(&Felt::ZERO), Some(Felt::ONE));
        assert!(Felt::MAX.checked_add(&Felt::ONE).is_none());
        assert!(Felt::ONE.checked_add(&(Felt::MAX)).is_none());
        // Mul
        assert_eq!(
            Felt::TWO.checked_mul(&Felt::THREE),
            Some(Felt::from_hex_unchecked("0x6"))
        );
        assert_eq!(Felt::TWO.checked_mul(&Felt::ZERO), Some(Felt::ZERO));
        assert!(Felt::MAX.checked_mul(&Felt::TWO).is_none());
        assert!(Felt::TWO.checked_mul(&Felt::MAX).is_none());
        // Sub
        assert_eq!(Felt::THREE.checked_sub(&Felt::TWO), Some(Felt::ONE));
        assert_eq!(Felt::THREE.checked_sub(&Felt::ZERO), Some(Felt::THREE));
        assert!(Felt::ONE.checked_sub(&Felt::TWO).is_none());
    }
}
