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
    fn test_poseidon_hash2() {
        // Test data generated from `cairo-lang` v0.11.0
        let test_data = [
            (
                Felt::from_hex("0xb662f9017fa7956fd70e26129b1833e10ad000fd37b4d9f4e0ce6884b7bbe")
                    .unwrap(),
                Felt::from_hex("0x1fe356bf76102cdae1bfbdc173602ead228b12904c00dad9cf16e035468bea")
                    .unwrap(),
                Felt::from_hex("0x75540825a6ecc5dc7d7c2f5f868164182742227f1367d66c43ee51ec7937a81")
                    .unwrap(),
            ),
            (
                Felt::from_hex("0xf4e01b2032298f86b539e3d3ac05ced20d2ef275273f9325f8827717156529")
                    .unwrap(),
                Felt::from_hex("0x587bc46f5f58e0511b93c31134652a689d761a9e7f234f0f130c52e4679f3a")
                    .unwrap(),
                Felt::from_hex("0xbdb3180fdcfd6d6f172beb401af54dd71b6569e6061767234db2b777adf98b")
                    .unwrap(),
            ),
        ];

        for (x, y, expected_hash) in test_data.into_iter() {
            let computed_hash = Poseidon::hash(&x, &y);
            assert_eq!(
                computed_hash, expected_hash,
                "Hash mismatch for inputs {:?} and {:?}",
                x, y
            );
        }
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
    fn test_poseidon_hash_array2() {
        let test_data = [
            (
                vec![
                    Felt::from_hex(
                        "0x9bf52404586087391c5fbb42538692e7ca2149bac13c145ae4230a51a6fc47",
                    )
                    .unwrap(),
                    Felt::from_hex(
                        "0x40304159ee9d2d611120fbd7c7fb8020cc8f7a599bfa108e0e085222b862c0",
                    )
                    .unwrap(),
                    Felt::from_hex(
                        "0x46286e4f3c450761d960d6a151a9c0988f9e16f8a48d4c0a85817c009f806a",
                    )
                    .unwrap(),
                ],
                Felt::from_hex("0x1ec38b38dc88bac7b0ed6ff6326f975a06a59ac601b417745fd412a5d38e4f7")
                    .unwrap(),
            ),
            (
                vec![
                    Felt::from_hex(
                        "0xbdace8883922662601b2fd197bb660b081fcf383ede60725bd080d4b5f2fd3",
                    )
                    .unwrap(),
                    Felt::from_hex(
                        "0x1eb1daaf3fdad326b959dec70ced23649cdf8786537cee0c5758a1a4229097",
                    )
                    .unwrap(),
                    Felt::from_hex(
                        "0x869ca04071b779d6f940cdf33e62d51521e19223ab148ef571856ff3a44ff1",
                    )
                    .unwrap(),
                    Felt::from_hex(
                        "0x533e6df8d7c4b634b1f27035c8676a7439c635e1fea356484de7f0de677930",
                    )
                    .unwrap(),
                ],
                Felt::from_hex("0x2520b8f910174c3e650725baacad4efafaae7623c69a0b5513d75e500f36624")
                    .unwrap(),
            ),
        ];

        for (input, expected_hash) in test_data.into_iter() {
            let actual_hash = Poseidon::hash_array(&input);
            assert_eq!(actual_hash, expected_hash);
        }
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
