#[cfg(feature = "alloc")]
pub extern crate alloc;
use core::str::FromStr;

use crate::felt::Felt;

#[cfg(feature = "alloc")]
mod alloc_impls;
#[cfg(feature = "devnet")]
use crate::short_string::ShortString;
#[cfg(feature = "alloc")]
pub use alloc_impls::*;

#[derive(Debug, Clone)]
pub enum ChainId {
    Mainnet,
    Sepolia,
    #[cfg(feature = "devnet")]
    Devnet(ShortString),
}

pub const SN_MAIN_STR: &str = "SN_MAIN";
pub const SN_MAIN: Felt = Felt::from_raw([
    502562008147966918,
    18446744073709551615,
    18446744073709551615,
    17696389056366564951,
]);

pub const SN_SEPOLIA_STR: &str = "SN_SEPOLIA";
pub const SN_SEPOLIA: Felt = Felt::from_raw([
    507980251676163170,
    18446744073709551615,
    18446744073708869172,
    1555806712078248243,
]);

impl core::fmt::Display for ChainId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ChainId::Mainnet => core::fmt::Display::fmt(SN_MAIN_STR, f),
            ChainId::Sepolia => core::fmt::Display::fmt(SN_SEPOLIA_STR, f),
            #[cfg(feature = "devnet")]
            ChainId::Devnet(ss) => core::fmt::Display::fmt(ss, f),
        }
    }
}

// Felt

impl From<ChainId> for Felt {
    fn from(value: ChainId) -> Self {
        match value {
            ChainId::Mainnet => SN_MAIN,
            ChainId::Sepolia => SN_SEPOLIA,
            #[cfg(feature = "devnet")]
            ChainId::Devnet(id) => id.into(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[cfg(not(feature = "devnet"))]
pub struct TryChainIdFormFeltError(Felt);

#[derive(Debug, Clone, Copy)]
#[cfg(feature = "devnet")]
pub struct TryChainIdFormFeltError(crate::short_string::TryShortStringFromFeltError, Felt);

impl core::fmt::Display for TryChainIdFormFeltError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        #[cfg(not(feature = "devnet"))]
        write!(f, "unknown chain id `{:#}`", self.0)?;

        #[cfg(feature = "devnet")]
        write!(
            f,
            "invalid felt for chain id `{}`. Must be a valid ShortString: {}",
            self.1, self.0
        )?;

        Ok(())
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryChainIdFormFeltError {}

impl TryFrom<Felt> for ChainId {
    type Error = TryChainIdFormFeltError;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        if value == SN_MAIN {
            return Ok(ChainId::Mainnet);
        }
        if value == SN_SEPOLIA {
            return Ok(ChainId::Sepolia);
        }

        #[cfg(feature = "devnet")]
        match ShortString::try_from(value) {
            Ok(ss) => Ok(ChainId::Devnet(ss)),
            Err(e) => Err(TryChainIdFormFeltError(e, value)),
        }

        #[cfg(not(feature = "devnet"))]
        Err(TryChainIdFormFeltError(value))
    }
}

// str

#[derive(Debug, Clone, Copy)]
#[cfg(feature = "devnet")]
pub struct TryChainIdFromStrError(crate::short_string::TryShortStringFromStringError);

#[derive(Debug, Clone)]
#[cfg(all(not(feature = "devnet"), feature = "alloc"))]
pub struct TryChainIdFromStrError(alloc::string::String);

#[derive(Debug, Clone)]
#[cfg(all(not(feature = "devnet"), not(feature = "alloc")))]
pub struct TryChainIdFromStrError;

impl core::fmt::Display for TryChainIdFromStrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        #[cfg(feature = "devnet")]
        write!(f, "failed to parse string as ShortString: {}", self.0)?;

        #[cfg(all(not(feature = "devnet"), feature = "alloc"))]
        write!(f, "unknown chain id: {}", self.0)?;

        #[cfg(all(not(feature = "devnet"), not(feature = "alloc")))]
        write!(f, "unknown chain id")?;

        Ok(())
    }
}

impl FromStr for ChainId {
    type Err = TryChainIdFromStrError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if value == SN_MAIN_STR {
            return Ok(ChainId::Mainnet);
        } else if value == SN_SEPOLIA_STR {
            return Ok(ChainId::Sepolia);
        }

        #[cfg(feature = "devnet")]
        return match ShortString::from_str(value) {
            Ok(ss) => Ok(ChainId::Devnet(ss)),
            Err(e) => Err(TryChainIdFromStrError(e)),
        };

        #[cfg(all(not(feature = "devnet"), feature = "alloc"))]
        return Err(TryChainIdFromStrError(alloc::string::ToString::to_string(
            value,
        )));

        #[cfg(all(not(feature = "devnet"), not(feature = "alloc")))]
        return Err(TryChainIdFromStrError);
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use crate::{
        chain_id::{SN_MAIN_STR, SN_SEPOLIA_STR},
        felt::Felt,
    };

    use super::{ChainId, SN_MAIN, SN_SEPOLIA};

    #[test]
    fn felt_and_chain_id_round_trip() {
        let felt = SN_MAIN;
        let chain_id = ChainId::try_from(felt).unwrap();
        assert_eq!(Felt::from(chain_id), felt);

        let felt = SN_SEPOLIA;
        let chain_id = ChainId::try_from(felt).unwrap();
        assert_eq!(Felt::from(chain_id), felt);

        #[cfg(feature = "devnet")]
        {
            let felt = Felt::from_hex_unwrap("0x63616665");
            let chain_id = ChainId::try_from(felt).unwrap();
            assert_eq!(Felt::from(chain_id), felt);

            // Non ascii
            let felt = Felt::from_hex_unwrap("0x1234567890");
            assert!(ChainId::try_from(felt).is_err());
            // Non too long
            let felt = Felt::from_hex_unwrap(
                "0x6363636363636363636363636363636363636363636363636363636363636363",
            );
            assert!(ChainId::try_from(felt).is_err());
        }
    }

    #[test]
    fn str_and_chain_id_round_trip() {
        let s = SN_MAIN_STR;
        let chain_id = ChainId::from_str(s).unwrap();
        assert_eq!(chain_id.to_string(), s.to_string());

        let s = SN_SEPOLIA_STR;
        let chain_id = ChainId::from_str(s).unwrap();
        assert_eq!(chain_id.to_string(), s.to_string());

        #[cfg(not(feature = "devnet"))]
        {
            let s = "SN_DEVNET";
            assert!(ChainId::from_str(s).is_err());
        }
        #[cfg(feature = "devnet")]
        {
            let s = "SN_DEVNET";
            let chain_id = ChainId::from_str(s).unwrap();
            assert_eq!(s, chain_id.to_string());
            let s = "SN_DEVNET_LOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOONG";
            assert!(ChainId::from_str(s).is_err());
            let s = "SN_DEVNET_🌟";
            assert!(ChainId::from_str(s).is_err());
        }
    }
}
