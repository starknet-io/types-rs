use crate::felt::Felt;
use lambdaworks_crypto::hash::poseidon::{
    starknet::PoseidonCairoStark252, Poseidon as PoseidonLambdaworks,
};
use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};

use super::traits::StarkHash;

pub struct Poseidon;

impl StarkHash for Poseidon {
    /// Computes the Poseidon hash of two Felts, as defined
    /// in <https://docs.starknet.io/documentation/architecture_and_concepts/Hashing/hash-functions/#poseidon_hash.>
    fn hash(felt_0: &Felt, felt_1: &Felt) -> Felt {
        Felt(PoseidonCairoStark252::hash(&felt_0.0, &felt_1.0))
    }
    /// Computes the Poseidon hash of an array of Felts, as defined
    /// in <https://docs.starknet.io/documentation/architecture_and_concepts/Cryptography/hash-functions/#poseidon_array_hash.>
    fn hash_array(felts: &[Felt]) -> Felt {
        // Non-copy but less dangerous than transmute
        // https://doc.rust-lang.org/std/mem/fn.transmute.html#alternatives
        Felt(PoseidonCairoStark252::hash_many(unsafe {
            core::slice::from_raw_parts(
                felts.as_ptr() as *const FieldElement<Stark252PrimeField>,
                felts.len(),
            )
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poseidon_hash() {
        let x =
            Felt::from_hex("0x03d937c035c878245caf64531a5756109c53068da139362728feb561405371cb")
                .unwrap();
        let y =
            Felt::from_hex("0x0208a0a10250e382e1e4bbe2880906c2791bf6275695e02fbbc6aeff9cd8b31a")
                .unwrap();

        assert_eq!(
            Poseidon::hash(&x, &y),
            Felt::from_hex("0x67c6a2e2d0c7867f97444ae17956dbc89d40ad22255bb06f5f6c515958926ed")
                .unwrap()
        );
    }

    #[test]
    fn test_poseidon_hash_array() {
        let a = Felt::from_hex("0xaa").unwrap();
        let b = Felt::from_hex("0xbb").unwrap();
        let c = Felt::from_hex("0xcc").unwrap();
        let expected =
            Felt::from_hex("0x2742e049f7e1613e4a014efeec0d742882a798ae0af8b8dd730358c23848775")
                .unwrap();
        assert_eq!(Poseidon::hash_array(&[a, b, c]), expected);
    }
}
