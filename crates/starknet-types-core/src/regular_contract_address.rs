//! A regular Starknet contract address
//!
//! This excludes the two special values reserved by the protocol: 0x0 and 0x1.
//! 0x0 is the default caller address used for external calls. Nothing is ever stored there.
//! 0x1 is used for block hash mapping.
//! See: https://docs.starknet.io/learn/protocol/state#special-addresses
//!
//! Most user applications should not interact with those special addresses.
//! Doing so would be a bug or invalid input.
//! `RegularContractAddress` enforces this at the type level.

use core::str::FromStr;

use crate::{
    contract_address::ContractAddress,
    felt::Felt,
    patricia_key::{
        PatriciaKey, PatriciaKeyFromFeltError, PatriciaKeyFromStrError, PATRICIA_KEY_UPPER_BOUND,
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
pub struct RegularContractAddress(ContractAddress);

impl core::fmt::Display for RegularContractAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<Felt> for RegularContractAddress {
    fn as_ref(&self) -> &Felt {
        self.0.as_ref()
    }
}

impl From<RegularContractAddress> for Felt {
    fn from(value: RegularContractAddress) -> Self {
        value.0.into()
    }
}

impl AsRef<PatriciaKey> for RegularContractAddress {
    fn as_ref(&self) -> &PatriciaKey {
        self.0.as_ref()
    }
}

impl From<RegularContractAddress> for PatriciaKey {
    fn from(value: RegularContractAddress) -> Self {
        value.0.into()
    }
}

impl AsRef<ContractAddress> for RegularContractAddress {
    fn as_ref(&self) -> &ContractAddress {
        &self.0
    }
}

impl From<RegularContractAddress> for ContractAddress {
    fn from(value: RegularContractAddress) -> Self {
        value.0
    }
}

/// In Starknet, contract addresses must follow specific constraints to be less than 2^251 (0x800000000000000000000000000000000000000000000000000000000000000) to be valid.
/// But there is also two special addressed for the protocol use:
///   * 0x0 acts as the default caller address for external calls and has no storage
///   * 0x1 functions as a storage space for block mapping
///
/// Making the regular contract address range be [2, 2^251)
#[derive(Debug, Clone, Copy)]
pub enum RegularContractAddressFromContractAddressError {
    Zero,
    One,
}

impl core::fmt::Display for RegularContractAddressFromContractAddressError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RegularContractAddressFromContractAddressError::Zero => {
                write!(
                    f,
                    "address 0x0 is reserved as the default caller address and has no storage"
                )
            }
            RegularContractAddressFromContractAddressError::One => {
                write!(
                    f,
                    "address 0x1 is reserved as storage space for block mapping"
                )
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for RegularContractAddressFromContractAddressError {}

impl TryFrom<ContractAddress> for RegularContractAddress {
    type Error = RegularContractAddressFromContractAddressError;

    fn try_from(value: ContractAddress) -> Result<Self, Self::Error> {
        if AsRef::<Felt>::as_ref(&value) == &Felt::ZERO {
            return Err(RegularContractAddressFromContractAddressError::Zero);
        }
        if AsRef::<Felt>::as_ref(&value) == &Felt::ONE {
            return Err(RegularContractAddressFromContractAddressError::One);
        }

        Ok(RegularContractAddress(value))
    }
}

#[derive(Debug, Clone, Copy)]
pub enum RegularContractAddressFromFeltError {
    TooBig(PatriciaKeyFromFeltError),
    SpecialAddress(RegularContractAddressFromContractAddressError),
}

impl core::fmt::Display for RegularContractAddressFromFeltError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RegularContractAddressFromFeltError::TooBig(e) => {
                write!(f, "invalid contract address: {}", e)
            }
            RegularContractAddressFromFeltError::SpecialAddress(e) => {
                write!(f, "got special contract address: {e}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for RegularContractAddressFromFeltError {}

impl Felt {
    /// Validates that a Felt value represents a valid Starknet contract address,
    /// excluding the two starknet special constract address `0x0` and `0x1`.
    ///
    /// https://docs.starknet.io/learn/protocol/state#special-addresses
    pub fn is_regular_contract_address(&self) -> bool {
        self >= &Felt::TWO && self < &PATRICIA_KEY_UPPER_BOUND
    }
}

impl TryFrom<Felt> for RegularContractAddress {
    type Error = RegularContractAddressFromFeltError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        let contract_address = ContractAddress::try_from(value)
            .map_err(RegularContractAddressFromFeltError::TooBig)?;

        Ok(RegularContractAddress(contract_address))
    }
}

#[derive(Debug)]
pub enum RegularContractAddressFromStrError {
    BadContractAddress(PatriciaKeyFromStrError),
    SpecialContractAddressZero,
    SpecialContractAddressOne,
}

impl core::fmt::Display for RegularContractAddressFromStrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RegularContractAddressFromStrError::BadContractAddress(e) => {
                write!(f, "invalid felt string: {e}")
            }
            RegularContractAddressFromStrError::SpecialContractAddressZero => write!(
                f,
                "address 0x0 is reserved as the default caller address and has no storage"
            ),
            RegularContractAddressFromStrError::SpecialContractAddressOne => write!(
                f,
                "address 0x1 is reserved as storage space for block mapping"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for RegularContractAddressFromStrError {}

impl FromStr for RegularContractAddress {
    type Err = RegularContractAddressFromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let contract_address = ContractAddress::from_str(s)
            .map_err(RegularContractAddressFromStrError::BadContractAddress)?;

        if AsRef::<Felt>::as_ref(&contract_address) == &Felt::ZERO {
            return Err(RegularContractAddressFromStrError::SpecialContractAddressZero);
        }
        if AsRef::<Felt>::as_ref(&contract_address) == &Felt::ONE {
            return Err(RegularContractAddressFromStrError::SpecialContractAddressOne);
        }

        Ok(RegularContractAddress(contract_address))
    }
}

impl RegularContractAddress {
    pub const fn from_hex_unwrap(s: &'static str) -> RegularContractAddress {
        let contract_address = ContractAddress::from_hex_unwrap(s);

        RegularContractAddress(contract_address)
    }
}
