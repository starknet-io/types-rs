use crate::felt::Felt;
use lambdaworks_crypto::hash::poseidon::{
    Poseidon as PoseidonLambdaworks, starknet::PoseidonCairoStark252,
};
use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};

use super::traits::StarkHash;

pub struct Poseidon;

impl StarkHash for Poseidon {
    /// Computes the Poseidon hash of two Felts, as defined
    /// in <https://docs.starknet.io/architecture/cryptography/#poseidon_hash>
    fn hash(felt_0: &Felt, felt_1: &Felt) -> Felt {
        Felt(PoseidonCairoStark252::hash(&felt_0.0, &felt_1.0))
    }
    /// Computes the Poseidon hash of an array of Felts, as defined
    /// in <https://docs.starknet.io/architecture/cryptography/#array_hashing_2>
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

    fn hash_single(felt: &Felt) -> Felt {
        Felt(PoseidonCairoStark252::hash_single(&felt.0))
    }
}

impl Poseidon {
    /// Computes the Hades permutation over a mutable state of 3 Felts, as defined
    /// in <https://docs.starknet.io/documentation/architecture_and_concepts/Cryptography/hash-functions/#poseidon_array_hash>
    pub fn hades_permutation(state: &mut [Felt; 3]) {
        let mut state_inner = [state[0].0, state[1].0, state[2].0];
        PoseidonCairoStark252::hades_permutation(&mut state_inner);
        for i in 0..3 {
            state[i] = Felt(state_inner[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poseidon_single() {
        let x = Felt::from_hex("0x9").unwrap();

        assert_eq!(
            Poseidon::hash_single(&x),
            Felt::from_hex("0x3bb3b91c714cb47003947f36dadc98326176963c434cd0a10320b8146c948b3")
                .unwrap()
        );
    }

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

    #[test]
    fn test_hades_permutation() {
        let mut state = [
            Felt::from_hex("0x9").unwrap(),
            Felt::from_hex("0xb").unwrap(),
            Felt::from_hex("0x2").unwrap(),
        ];
        let expected = [
            Felt::from_hex("0x510f3a3faf4084e3b1e95fd44c30746271b48723f7ea9c8be6a9b6b5408e7e6")
                .unwrap(),
            Felt::from_hex("0x4f511749bd4101266904288021211333fb0a514cb15381af087462fa46e6bd9")
                .unwrap(),
            Felt::from_hex("0x186f6dd1a6e79cb1b66d505574c349272cd35c07c223351a0990410798bb9d8")
                .unwrap(),
        ];
        Poseidon::hades_permutation(&mut state);

        assert_eq!(state, expected);
    }
}
