use num_bigint::{BigInt, BigUint, ToBigInt, ToBigUint};
use num_traits::{FromPrimitive, ToPrimitive};

use super::U256;

impl ToBigUint for U256 {
    fn to_biguint(&self) -> Option<BigUint> {
        let mut buffer = [0u8; 32];

        buffer[..16].copy_from_slice(&self.high.to_be_bytes());
        buffer[16..].copy_from_slice(&self.low.to_be_bytes());

        Some(BigUint::from_bytes_be(&buffer))
    }
}

impl ToBigInt for U256 {
    fn to_bigint(&self) -> Option<BigInt> {
        self.to_biguint().map(|v| v.into())
    }
}

impl FromPrimitive for U256 {
    fn from_i64(value: i64) -> Option<Self> {
        value.try_into().ok()
    }

    fn from_u64(value: u64) -> Option<Self> {
        Some(value.into())
    }
    fn from_i128(value: i128) -> Option<Self> {
        value.try_into().ok()
    }

    fn from_u128(value: u128) -> Option<Self> {
        Some(value.into())
    }
}

impl ToPrimitive for U256 {
    fn to_i64(&self) -> Option<i64> {
        (*self).try_into().ok()
    }

    fn to_u64(&self) -> Option<u64> {
        (*self).try_into().ok()
    }

    fn to_i128(&self) -> Option<i128> {
        (*self).try_into().ok()
    }

    fn to_u128(&self) -> Option<u128> {
        (*self).try_into().ok()
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;

    #[test]
    fn to_bigint() {
        let big_value =
            "115000000000000000000000000000000000000000000000000000000000000000000000000000";
        let bigint = BigInt::from_str(big_value).unwrap();
        let u256 = U256::from_dec_str(big_value).unwrap();
        let converted = u256.to_bigint().unwrap();
        assert_eq!(bigint, converted);
    }
    #[test]
    fn to_biguint() {
        let big_value =
            "115000000000000000000000000000000000000000000000000000000000000000000000000000";
        let biguint = BigInt::from_str(big_value).unwrap();
        let u256 = U256::from_dec_str(big_value).unwrap();
        let converted = u256.to_bigint().unwrap();
        assert_eq!(biguint, converted);
    }
}
