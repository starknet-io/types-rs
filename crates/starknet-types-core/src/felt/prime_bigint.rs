use crate::felt::Felt;
use lazy_static::lazy_static;
use num_bigint::{BigInt, BigUint};
use num_traits::Num;

lazy_static! {
    pub static ref CAIRO_PRIME_BIGINT: BigInt = BigInt::from_str_radix(
        "800000000000011000000000000000000000000000000000000000000000001",
        16
    )
    .unwrap();
}

impl Felt {
    pub fn prime() -> BigUint {
        (*CAIRO_PRIME_BIGINT).to_biguint().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prime() {
        assert_eq!(Felt::prime(), CAIRO_PRIME_BIGINT.to_biguint().unwrap());
    }
}
