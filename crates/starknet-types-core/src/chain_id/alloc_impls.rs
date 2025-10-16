#[cfg(not(feature = "std"))]
pub extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::string::{String, ToString};

use crate::short_string;
use crate::short_string::ShortString;

use super::{ChainId, SN_MAIN_STR, SN_SEPOLIA_STR};

impl From<ChainId> for ShortString {
    fn from(value: ChainId) -> Self {
        match value {
            ChainId::Mainnet => short_string!("SN_MAIN"),
            ChainId::Sepolia => short_string!("SN_SEPOLIA"),
            #[cfg(feature = "devnet")]
            ChainId::Devnet(ss) => ss,
        }
    }
}

#[cfg(feature = "devnet")]
impl From<ShortString> for ChainId {
    fn from(value: ShortString) -> Self {
        match value.as_str() {
            SN_MAIN_STR => ChainId::Mainnet,
            SN_SEPOLIA_STR => ChainId::Sepolia,
            _ => ChainId::Devnet(value),
        }
    }
}

#[cfg(not(feature = "devnet"))]
mod try_chain_id_from_short_string {
    use crate::chain_id::{SN_MAIN_STR, SN_SEPOLIA_STR};

    use super::*;

    #[derive(Debug, Clone)]
    pub struct TryChainIdFromShortStringError(ShortString);

    impl core::fmt::Display for TryChainIdFromShortStringError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "unknown chain id: {}", self.0)
        }
    }

    #[cfg(feature = "std")]
    impl std::error::Error for TryChainIdFromShortStringError {}

    impl TryFrom<ShortString> for ChainId {
        type Error = TryChainIdFromShortStringError;

        fn try_from(value: ShortString) -> Result<Self, Self::Error> {
            match value.as_str() {
                SN_MAIN_STR => Ok(ChainId::Mainnet),
                SN_SEPOLIA_STR => Ok(ChainId::Sepolia),
                _ => Err(TryChainIdFromShortStringError(value)),
            }
        }
    }
}
#[cfg(not(feature = "devnet"))]
pub use try_chain_id_from_short_string::*;

// String

impl From<ChainId> for String {
    fn from(value: ChainId) -> Self {
        match value {
            ChainId::Mainnet => SN_MAIN_STR.to_string(),
            ChainId::Sepolia => SN_SEPOLIA_STR.to_string(),
            #[cfg(feature = "devnet")]
            ChainId::Devnet(ss) => ss.to_string(),
        }
    }
}

#[cfg(not(feature = "devnet"))]
impl From<ChainId> for &'static str {
    fn from(value: ChainId) -> Self {
        match value {
            ChainId::Mainnet => SN_MAIN_STR,
            ChainId::Sepolia => SN_SEPOLIA_STR,
        }
    }
}

#[cfg(feature = "devnet")]
impl<'a> From<&'a ChainId> for &'a str {
    fn from(value: &'a ChainId) -> Self {
        match value {
            ChainId::Mainnet => SN_MAIN_STR,
            ChainId::Sepolia => SN_SEPOLIA_STR,
            ChainId::Devnet(ss) => ss.as_ref(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[cfg(feature = "devnet")]
pub struct TryChainIdFromStringError(pub(super) crate::short_string::TryShortStringFromStringError);

#[derive(Debug, Clone)]
#[cfg(not(feature = "devnet"))]
pub struct TryChainIdFromStringError(pub(super) String);

impl core::fmt::Display for TryChainIdFromStringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        #[cfg(feature = "devnet")]
        write!(f, "failed to parse string as ShortString: {}", self.0)?;

        #[cfg(not(feature = "devnet"))]
        write!(f, "unknown chain id: {}", self.0)?;

        Ok(())
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryChainIdFromStringError {}

impl TryFrom<String> for ChainId {
    type Error = TryChainIdFromStringError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        match value.as_str() {
            SN_MAIN_STR => Ok(ChainId::Mainnet),
            SN_SEPOLIA_STR => Ok(ChainId::Sepolia),
            _ => {
                #[cfg(feature = "devnet")]
                match ShortString::try_from(value) {
                    Ok(ss) => Ok(ChainId::Devnet(ss)),
                    Err(e) => Err(TryChainIdFromStringError(e)),
                }

                #[cfg(not(feature = "devnet"))]
                Err(TryChainIdFromStringError(value))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_string_and_chain_id_round_trip() {
        let ss = short_string!("SN_MAIN");
        let chain_id = ChainId::try_from(ss.clone()).unwrap();
        assert_eq!(chain_id.to_string(), ss.to_string());

        let ss = short_string!("SN_SEPOLIA");
        let chain_id = ChainId::try_from(ss.clone()).unwrap();
        assert_eq!(chain_id.to_string(), ss.to_string());

        #[cfg(not(feature = "devnet"))]
        {
            let ss = short_string!("SN_DEVNET");
            assert!(ChainId::try_from(ss).is_err());
        }
        #[cfg(feature = "devnet")]
        {
            let ss = short_string!("SN_DEVNET");
            let chain_id = ChainId::try_from(ss.clone()).unwrap();
            assert_eq!(ss.to_string(), chain_id.to_string());
        }
    }

    #[test]
    fn string_and_chain_id_round_trip() {
        let s = String::from(SN_MAIN_STR);
        let chain_id = ChainId::try_from(s.clone()).unwrap();
        assert_eq!(chain_id.to_string(), s.to_string());

        let s = String::from(SN_SEPOLIA_STR);
        let chain_id = ChainId::try_from(s.clone()).unwrap();
        assert_eq!(chain_id.to_string(), s.to_string());

        #[cfg(not(feature = "devnet"))]
        {
            let s = String::from("SN_DEVNET");
            assert!(ChainId::try_from(s).is_err());
        }
        #[cfg(feature = "devnet")]
        {
            let s = String::from("SN_DEVNET");
            let chain_id = ChainId::try_from(s.clone()).unwrap();
            assert_eq!(s, chain_id.to_string());

            let s = String::from("SN_DEVNET_LOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOONG");
            assert!(ChainId::try_from(s).is_err());
            let s = String::from("SN_DEVNET_🌟");
            assert!(ChainId::try_from(s).is_err());
        }
    }
}
