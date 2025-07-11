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

    #[test]
    fn bigints_to_felt() {
        let one = &*CAIRO_PRIME_BIGINT + BigInt::from(1_u32);
        assert_eq!(Felt::from(&one.to_biguint().unwrap()), Felt::from(1));
        assert_eq!(Felt::from(&one), Felt::from(1));

        let zero = &*CAIRO_PRIME_BIGINT * 99_u32;
        assert_eq!(Felt::from(&zero.to_biguint().unwrap()), Felt::from(0));
        assert_eq!(Felt::from(&zero), Felt::from(0));

        assert_eq!(
            Felt::from(&BigInt::from(-1)),
            Felt::from_hex("0x800000000000011000000000000000000000000000000000000000000000000")
                .unwrap()
        );

        let numbers_str = [
            "0x0",
            "0x1",
            "0x10",
            "0x8000000000000110000000000",
            "0xffffffffffffff",
            "0xffffffffefff12380777abcd",
        ];

        for number_str in numbers_str {
            assert_eq!(
                Felt::from(&BigInt::from_str_radix(&number_str[2..], 16).unwrap()),
                Felt::from_hex(number_str).unwrap()
            );
            assert_eq!(
                Felt::from(&BigUint::from_str_radix(&number_str[2..], 16).unwrap()),
                Felt::from_hex(number_str).unwrap()
            )
        }
    }
}
