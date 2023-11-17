use crate::felt::Felt;
use lambdaworks_crypto::hash::pedersen::Pedersen as PedersenLambdaworks;
use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};

use super::traits::StarkHash;

pub struct Pedersen;

impl StarkHash for Pedersen {
    /// Computes the Pedersen hash of two Felts, as defined
    /// in <https://docs.starknet.io/documentation/architecture_and_concepts/Hashing/hash-functions/#pedersen_hash.>
    fn hash(felt_0: &Felt, felt_1: &Felt) -> Felt {
        let pedersen = PedersenLambdaworks::default();

        let hash = pedersen.hash(&felt_0.0, &felt_1.0);

        Felt(hash)
    }

    /// Computes the Pedersen hash of an array of Felts, as defined
    /// in <https://docs.starknet.io/documentation/architecture_and_concepts/Hashing/hash-functions/#array_hashing.>
    fn hash_array(felts: &[Felt]) -> Felt {
        let pedersen = PedersenLambdaworks::default();
        let data_len = Felt::from(felts.len());
        let current_hash: FieldElement<Stark252PrimeField> = felts.iter().fold(
            FieldElement::<Stark252PrimeField>::zero(),
            |current_hash, felt| pedersen.hash(&current_hash, &felt.0),
        );
        Felt(pedersen.hash(&current_hash, &data_len.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
