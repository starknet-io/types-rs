use crate::felt::Felt;

pub trait StarkHash {
    /// Computes Pedersen hash using STARK curve on two elements, as defined
    /// in <https://docs.starknet.io/documentation/architecture_and_concepts/Hashing/hash-functions/#pedersen_hash.>
    fn hash(&self, felt_0: &Felt, felt_1: &Felt) -> Felt;

    /// Computes Pedersen hash using STARK curve on an array of elements, as defined
    /// in <https://docs.starknet.io/documentation/architecture_and_concepts/Hashing/hash-functions/#array_hashing.>
    fn hash_array(&self, felts: &[Felt]) -> Felt;
}
