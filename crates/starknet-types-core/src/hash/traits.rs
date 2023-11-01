use crate::felt::Felt;

pub trait StarkHash {
    /// Computes the hash of two Felt
    fn hash(felt_0: &Felt, felt_1: &Felt) -> Felt;

    /// Computes the hash of an array of Felts,
    /// as defined in <https://docs.starknet.io/documentation/architecture_and_concepts/Hashing/hash-functions/#array_hashing.>
    fn hash_array(felts: &[Felt]) -> Felt;
}
