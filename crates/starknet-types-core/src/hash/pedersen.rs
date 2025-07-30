use crate::felt::Felt;
use lambdaworks_crypto::hash::pedersen::{Pedersen as PedersenLambdaworks, PedersenStarkCurve};
use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};

use super::traits::StarkHash;

pub struct Pedersen;

impl StarkHash for Pedersen {
    /// Computes the Pedersen hash of two Felts, as defined
    /// in <https://docs.starknet.io/architecture/cryptography/#pedersen_hash>
    fn hash(felt_0: &Felt, felt_1: &Felt) -> Felt {
        Felt(PedersenStarkCurve::hash(&felt_0.0, &felt_1.0))
    }

    /// Computes the Pedersen hash of an array of Felts, as defined
    /// in <https://docs.starknet.io/architecture/cryptography/#array_hashing>
    ///
    /// Warning: there is room for collision as:
    /// Pedersen::hash_array([value]) and Pedersen::hash(Pedersen::hash(0, value), 1) will return the same values
    fn hash_array(felts: &[Felt]) -> Felt {
        let data_len = Felt::from(felts.len());
        let current_hash: FieldElement<Stark252PrimeField> = felts
            .iter()
            .fold(FieldElement::zero(), |current_hash, felt| {
                PedersenStarkCurve::hash(&current_hash, &felt.0)
            });
        Felt(PedersenStarkCurve::hash(&current_hash, &data_len.0))
    }

    /// Computes the Pedersen hash of a single Felt
    ///
    /// Warning: there is room for collision as:
    /// Pedersen::hash_single(value) and Pedersen::hash(value, 0) will return the same values
    fn hash_single(felt: &Felt) -> Felt {
        Felt(PedersenStarkCurve::hash(&felt.0, &Felt::from(0).0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pedersen_hash_single() {
        let x =
            Felt::from_hex("0x03d937c035c878245caf64531a5756109c53068da139362728feb561405371cb")
                .unwrap();
        assert_eq!(
            Pedersen::hash_single(&x),
            Felt::from_hex("0x460ded9dacd215bcfc43f1b30b2a02690378e00f82a2283617d47d948c7b7f1")
                .unwrap()
        )
    }

    #[test]
    fn test_pedersen_hash_collision() {
        let x =
            Felt::from_hex("0x03d937c035c878245caf64531a5756109c53068da139362728feb561405371cb")
                .unwrap();
        assert_eq!(
            Pedersen::hash_single(&x),
            Pedersen::hash(&x, &Felt::from(0))
        )
    }

    #[test]
    fn test_pedersen_hash() {
        let x =
            Felt::from_hex("0x03d937c035c878245caf64531a5756109c53068da139362728feb561405371cb")
                .unwrap();
        let y =
            Felt::from_hex("0x0208a0a10250e382e1e4bbe2880906c2791bf6275695e02fbbc6aeff9cd8b31a")
                .unwrap();

        assert_eq!(
            Pedersen::hash(&x, &y),
            Felt::from_hex("0x030e480bed5fe53fa909cc0f8c4d99b8f9f2c016be4c41e13a4848797979c662")
                .unwrap()
        );
    }

    #[test]
    fn test_pedersen_hash_array() {
        let a = Felt::from_hex("0xaa").unwrap();
        let b = Felt::from_hex("0xbb").unwrap();
        let c = Felt::from_hex("0xcc").unwrap();
        let expected =
            Felt::from_hex("0x10808e8929644950878c4f71326e47c6b584d9cfea2de0415daf8def0f5e89f")
                .unwrap();
        assert_eq!(Pedersen::hash_array(&[a, b, c]), expected);
    }
}
