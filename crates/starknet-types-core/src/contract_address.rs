//! A starknet contract address
//!
//! In starknet valid contract addresses exists as a subset of the type `Felt`.
//! Therefore some checks must be done in order to produce protocol valid addresses.
//! This module provides this logic as a type `ContractAddress`, that can garantee the validity of the address.
//! It also comes with some quality of life methods.

use core::str::FromStr;

use crate::{
    felt::Felt,
    patricia_key::{PatriciaKey, PatriciaKeyFromFeltError, PatriciaKeyFromStrError},
};

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(
    feature = "parity-scale-codec",
    derive(parity_scale_codec::Encode, parity_scale_codec::Decode)
)]
pub struct ContractAddress(PatriciaKey);

impl ContractAddress {
    pub const ZERO: Self = Self::from_hex_unchecked("0x0");
    pub const ONE: Self = Self::from_hex_unchecked("0x1");
    pub const TWO: Self = Self::from_hex_unchecked("0x2");
    pub const THREE: Self = Self::from_hex_unchecked("0x3");

    /// Lower inclusive bound
    pub const LOWER_BOUND: Self = Self::ZERO;
    /// Upper non-inclusive bound
    pub const UPPER_BOUND: Self = Self(PatriciaKey::UPPER_BOUND);
}

impl core::fmt::Display for ContractAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<Felt> for ContractAddress {
    fn as_ref(&self) -> &Felt {
        self.0.as_ref()
    }
}

impl From<ContractAddress> for Felt {
    fn from(value: ContractAddress) -> Self {
        value.0.into()
    }
}

impl AsRef<PatriciaKey> for ContractAddress {
    fn as_ref(&self) -> &PatriciaKey {
        &self.0
    }
}

impl From<ContractAddress> for PatriciaKey {
    fn from(value: ContractAddress) -> Self {
        value.0
    }
}

impl From<PatriciaKey> for ContractAddress {
    fn from(value: PatriciaKey) -> Self {
        ContractAddress(value)
    }
}

impl TryFrom<Felt> for ContractAddress {
    type Error = PatriciaKeyFromFeltError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        Ok(ContractAddress(PatriciaKey::try_from(value)?))
    }
}

impl Felt {
    /// Validates that a Felt value represents a valid Starknet contract address.
    pub fn is_valid_contract_address(&self) -> bool {
        self < &Felt::from(ContractAddress::UPPER_BOUND)
    }
}

impl FromStr for ContractAddress {
    type Err = PatriciaKeyFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(ContractAddress(PatriciaKey::from_str(s)?))
    }
}

impl ContractAddress {
    /// Create a new [ContractAddress] from an hex encoded string without checking it is a valid value.
    ///
    /// Should NEVER be used on user inputs,
    /// as it can cause erroneous execution if dynamically initialized with bad values.
    /// Should mostly be used at compilation time on hardcoded static string.
    pub const fn from_hex_unchecked(s: &'static str) -> ContractAddress {
        let patricia_key = PatriciaKey::from_hex_unchecked(s);

        ContractAddress(patricia_key)
    }
}

#[cfg(test)]
mod test {
    #[cfg(feature = "alloc")]
    pub extern crate alloc;
    use proptest::prelude::*;

    use crate::{
        contract_address::ContractAddress, felt::Felt, patricia_key::PATRICIA_KEY_UPPER_BOUND,
    };

    #[test]
    fn basic_values() {
        assert!(ContractAddress::try_from(PATRICIA_KEY_UPPER_BOUND).is_err());

        let felt = Felt::TWO;
        let contract_address = ContractAddress::try_from(felt).unwrap();
        assert_eq!(Felt::from(contract_address), felt);
    }

    proptest! {
        #[test]
        fn is_valid_match_try_into(ref x in any::<Felt>()) {
            if x.is_valid_contract_address() {
                prop_assert!(ContractAddress::try_from(*x).is_ok());
            } else {
                prop_assert!(ContractAddress::try_from(*x).is_err());
            }
        }
    }
}
