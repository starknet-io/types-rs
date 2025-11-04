//! A key used for nodes of a Patricia tree.
//!
//! The state of the starknet blockchain (contracts declared, contracts deployed, storage of each contract),
//! is represented as multiple binary Merkle-Patricia trees.
//! Those trees have an height of 251, which means that they contain at most 2^251 values.
//! The keys of those values are represented as `Felt`, with range [0, PATRICIA_KEY_UPPER_BOUND).
//! Therefore not every `Felt` is a valid `PatriciaKey`,
//! and we can use the `PatriciaKey` type to enfoce type safety in our code.
//!
//! See https://docs.starknet.io/learn/protocol/state for further details.

use core::str::FromStr;

use crate::felt::Felt;

pub const PATRICIA_KEY_UPPER_BOUND: PatriciaKey = PatriciaKey(Felt::from_hex_unwrap(
    "0x800000000000000000000000000000000000000000000000000000000000000",
));

/// The index upper bound for a Starknet tree
///
/// Equal to `0x800000000000000000000000000000000000000000000000000000000000000 - 256`.
///
/// In Starknet, users are allowed to store up to 256 felts in a tree leaf.
/// Therefore, storage addresses can be used as "pointers" to some specific felt stored in a leaf:
/// ValueAddress = LeafAddress + IndexInsideTheLeaf
/// So, all leaf addresses are modulo this value.
pub const STORAGE_LEAF_ADDRESS_UPPER_BOUND: PatriciaKey = PatriciaKey(Felt::from_raw([
    576459263475590224,
    18446744073709255680,
    160989183,
    18446743986131443745,
]));

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(
    feature = "parity-scale-codec",
    derive(parity_scale_codec::Encode, parity_scale_codec::Decode)
)]
pub struct PatriciaKey(Felt);

impl PatriciaKey {
    /// Lower inclusive bound
    pub const LOWER_BOUND: Self = Self(Felt::ZERO);
    /// Upper non-inclusive bound
    pub const UPPER_BOUND: Self = PATRICIA_KEY_UPPER_BOUND;
}

impl core::fmt::Display for PatriciaKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<Felt> for PatriciaKey {
    fn as_ref(&self) -> &Felt {
        &self.0
    }
}

impl From<PatriciaKey> for Felt {
    fn from(value: PatriciaKey) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PatriciaKeyFromFeltError(Felt);

impl core::fmt::Display for PatriciaKeyFromFeltError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        #[cfg(feature = "alloc")]
        return write!(
            f,
            "invalid felt value for patricia key. Upper non-inclusive bound is 2^251 got {:#x}",
            self.0
        );

        #[cfg(not(feature = "alloc"))]
        return write!(
            f,
            "invalid felt value for patricia key. Upper non-inclusive bound is 2^251 got {}",
            self.0
        );
    }
}

#[cfg(feature = "std")]
impl std::error::Error for PatriciaKeyFromFeltError {}

impl TryFrom<Felt> for PatriciaKey {
    type Error = PatriciaKeyFromFeltError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        if value >= PATRICIA_KEY_UPPER_BOUND.0 {
            return Err(PatriciaKeyFromFeltError(value));
        }

        Ok(PatriciaKey(value))
    }
}

#[derive(Debug)]
pub enum PatriciaKeyFromStrError {
    BadFelt(<Felt as FromStr>::Err),
    BadKey(PatriciaKeyFromFeltError),
}

impl core::fmt::Display for PatriciaKeyFromStrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PatriciaKeyFromStrError::BadFelt(e) => write!(f, "invalid felt string: {e}"),
            PatriciaKeyFromStrError::BadKey(e) => write!(f, "invalid address value: {e}"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for PatriciaKeyFromStrError {}

impl FromStr for PatriciaKey {
    type Err = PatriciaKeyFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let felt = Felt::from_str(s).map_err(PatriciaKeyFromStrError::BadFelt)?;
        let contract_address =
            PatriciaKey::try_from(felt).map_err(PatriciaKeyFromStrError::BadKey)?;

        Ok(contract_address)
    }
}

impl PatriciaKey {
    /// Create a new [PatriciaKey] from an hex encoded string without checking it is a valid value.
    ///
    /// Should NEVER be used on user inputs,
    /// as it can cause erroneous execution if dynamically initialized with bad values.
    /// Should mostly be used at compilation time on hardcoded static string.
    pub const fn from_hex_unchecked(s: &'static str) -> PatriciaKey {
        let felt = Felt::from_hex_unwrap(s);

        PatriciaKey(felt)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        felt::Felt,
        patricia_key::{PATRICIA_KEY_UPPER_BOUND, STORAGE_LEAF_ADDRESS_UPPER_BOUND},
    };

    #[test]
    fn enforce_max_storage_leaf_address() {
        assert_eq!(
            PATRICIA_KEY_UPPER_BOUND.0 - Felt::from(256),
            STORAGE_LEAF_ADDRESS_UPPER_BOUND.into(),
        );
    }
}
