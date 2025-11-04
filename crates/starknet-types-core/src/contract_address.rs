//! A starknet contract address
//!
//! In starknet valid contract addresses exist as a subset of the type `Felt`.
//! Therefore some checks must be done in order to produce protocol valid addresses.
//! This module provides this logic as a type `ContractAddress`, that can garantee the validity of the address.
//! It also comes with some quality of life methods.

use core::str::FromStr;

use crate::{
    felt::Felt,
    patricia_key::{
        PatriciaKey, PatriciaKeyFromFeltError, PatriciaKeyFromStrError,
        STORAGE_LEAF_ADDRESS_UPPER_BOUND,
    },
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
    ///
    /// For consistency with other merkle leaf bounds, [ContractAddress] is also bounded by [STORAGE_LEAF_ADDRESS_UPPER_BOUND]
    pub const UPPER_BOUND: Self = Self(STORAGE_LEAF_ADDRESS_UPPER_BOUND);
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

#[derive(Debug)]
pub enum ContractAddressFromPatriciaKeyError {
    OutOfBounds,
}

impl core::fmt::Display for ContractAddressFromPatriciaKeyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ContractAddressFromPatriciaKeyError::OutOfBounds => write!(
                f,
                "value out of bounds, upper non-inclusive bound is {}",
                ContractAddress::UPPER_BOUND
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ContractAddressFromPatriciaKeyError {}

impl TryFrom<PatriciaKey> for ContractAddress {
    type Error = ContractAddressFromPatriciaKeyError;

    fn try_from(value: PatriciaKey) -> Result<Self, Self::Error> {
        if value >= STORAGE_LEAF_ADDRESS_UPPER_BOUND {
            Err(ContractAddressFromPatriciaKeyError::OutOfBounds)
        } else {
            Ok(ContractAddress(value))
        }
    }
}

#[derive(Debug)]
pub enum ContractAddressFromFeltError {
    PatriciaKey(PatriciaKeyFromFeltError),
    OutOfBounds(ContractAddressFromPatriciaKeyError),
}

impl core::fmt::Display for ContractAddressFromFeltError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ContractAddressFromFeltError::OutOfBounds(e) => {
                write!(f, "invalid value for contract address: {e}")
            }
            ContractAddressFromFeltError::PatriciaKey(e) => {
                write!(f, "invalid patricia key value: {e}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ContractAddressFromFeltError {}
impl TryFrom<Felt> for ContractAddress {
    type Error = ContractAddressFromFeltError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        let pk = PatriciaKey::try_from(value).map_err(ContractAddressFromFeltError::PatriciaKey)?;
        let ca =
            ContractAddress::try_from(pk).map_err(ContractAddressFromFeltError::OutOfBounds)?;

        Ok(ca)
    }
}

impl Felt {
    /// Validates that a Felt value represents a valid Starknet contract address.
    pub fn is_valid_contract_address(&self) -> bool {
        self < &Felt::from(ContractAddress::UPPER_BOUND)
    }
}

#[derive(Debug)]
pub enum ContractAddressFromStrError {
    PatriciaKey(PatriciaKeyFromStrError),
    OutOfBounds(ContractAddressFromPatriciaKeyError),
}

impl core::fmt::Display for ContractAddressFromStrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ContractAddressFromStrError::PatriciaKey(e) => {
                write!(f, "invalid patricia key: {e}")
            }
            ContractAddressFromStrError::OutOfBounds(e) => {
                write!(f, "invalid value for contract address: {e}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ContractAddressFromStrError {}

impl FromStr for ContractAddress {
    type Err = ContractAddressFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let pk = PatriciaKey::from_str(s).map_err(ContractAddressFromStrError::PatriciaKey)?;
        let ca = ContractAddress::try_from(pk).map_err(ContractAddressFromStrError::OutOfBounds)?;

        Ok(ca)
    }
}

impl ContractAddress {
    /// Creates a new [ContractAddress] from an hex encoded string without checking it is a valid value.
    ///
    /// Should NEVER be used on user inputs, as it can cause erroneous execution if dynamically initialized with bad values.
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
