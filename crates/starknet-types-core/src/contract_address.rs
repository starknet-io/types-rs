//! A starknet contract address
//!
//! In starknet valid contract addresses exists as a subset of the type `Felt`.
//! Therefore some checks must be done in order to produce protocol valid addresses.
//! This module provides this logic as a type `ContractAddress`, that can garantee the validity of the address.
//! It also comes with some quality of life methods.

use core::str::FromStr;

use crate::{felt::Felt, patricia_key::PATRICIA_KEY_UPPER_BOUND};

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(
    feature = "parity-scale-codec",
    derive(parity_scale_codec::Encode, parity_scale_codec::Decode)
)]
pub struct ContractAddress(Felt);

impl core::fmt::Display for ContractAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<Felt> for ContractAddress {
    fn as_ref(&self) -> &Felt {
        &self.0
    }
}

impl From<ContractAddress> for Felt {
    fn from(value: ContractAddress) -> Self {
        value.0
    }
}

#[derive(Debug, Copy, Clone)]
/// In Starknet, contract addresses must follow specific constraints to be considered valid:
/// - They must be greater than or equal to 2, as addresses 0 and 1 are reserved for system use:
///   * 0x0 acts as the default caller address for external calls and has no storage
///   * 0x1 functions as a storage space for block mapping [link](https://docs.starknet.io/architecture-and-concepts/network-architecture/starknet-state/#special_addresses)
/// - They must be less than 2^251 (0x800000000000000000000000000000000000000000000000000000000000000)
///
/// Making the valid addressabe range be [2, 2^251)
pub enum ContactAddressFromFeltError {
    Zero,
    One,
    TooBig,
}

impl core::fmt::Display for ContactAddressFromFeltError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ContactAddressFromFeltError::Zero => {
                write!(
                    f,
                    "address 0x0 is reserved as the default caller address and has no storage"
                )
            }
            ContactAddressFromFeltError::One => {
                write!(
                    f,
                    "address 0x1 is reserved as storage space for block mapping"
                )
            }
            ContactAddressFromFeltError::TooBig => {
                write!(f, "the highest possible address is 2^251 - 1")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ContactAddressFromFeltError {}

/// Validates that a Felt value represents a valid Starknet contract address.
///
/// This validation is critical for preventing funds from being sent to invalid addresses,
/// which would result in permanent loss.
impl Felt {
    pub fn is_valid_contract_address(&self) -> bool {
        self >= &Felt::from(2u64) && self < &PATRICIA_KEY_UPPER_BOUND
    }
}

impl TryFrom<Felt> for ContractAddress {
    type Error = ContactAddressFromFeltError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        if value == Felt::ZERO {
            return Err(ContactAddressFromFeltError::Zero);
        }
        if value == Felt::ONE {
            return Err(ContactAddressFromFeltError::One);
        }
        if value >= PATRICIA_KEY_UPPER_BOUND {
            return Err(ContactAddressFromFeltError::TooBig);
        }

        Ok(ContractAddress(value))
    }
}

#[derive(Debug)]
pub enum ContractAddressFromStrError {
    BadFelt(<Felt as FromStr>::Err),
    BadAddress(ContactAddressFromFeltError),
}

impl core::fmt::Display for ContractAddressFromStrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ContractAddressFromStrError::BadFelt(e) => write!(f, "invalid felt string: {e}"),
            ContractAddressFromStrError::BadAddress(e) => write!(f, "invalid address value: {e}"),
        }
    }
}

impl FromStr for ContractAddress {
    type Err = ContractAddressFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let felt = Felt::from_str(s).map_err(ContractAddressFromStrError::BadFelt)?;
        let contract_address =
            ContractAddress::try_from(felt).map_err(ContractAddressFromStrError::BadAddress)?;

        Ok(contract_address)
    }
}

impl ContractAddress {
    pub const fn from_hex_unchecked(s: &'static str) -> ContractAddress {
        let felt = Felt::from_hex_unwrap(s);

        ContractAddress(felt)
    }
}

#[cfg(test)]
mod test {
    #[cfg(feature = "alloc")]
    pub extern crate alloc;
    use proptest::prelude::*;

    use crate::{
        contract_address::{ContractAddress, PATRICIA_KEY_UPPER_BOUND},
        felt::Felt,
    };

    #[test]
    fn basic_values() {
        assert!(ContractAddress::try_from(Felt::ZERO).is_err());
        assert!(ContractAddress::try_from(Felt::ONE).is_err());
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
