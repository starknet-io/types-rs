use crate::{felt::Felt, short_string, short_string::ShortString};

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

// ShortString

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
        if value.as_ref() == SN_MAIN_STR {
            ChainId::Mainnet
        } else if value.as_ref() == SN_SEPOLIA_STR {
            ChainId::Sepolia
        } else {
            ChainId::Devnet(value)
        }
    }
}

#[cfg(not(feature = "devnet"))]
mod try_chain_id_from_short_string {
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
            if value.as_ref() == SN_MAIN_STR {
                Ok(ChainId::Mainnet)
            } else if value.as_ref() == SN_SEPOLIA_STR {
                Ok(ChainId::Sepolia)
            } else {
                Err(TryChainIdFromShortStringError(value))
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
impl From<ChainId> for &str {
    fn from(value: ChainId) -> Self {
        match value {
            ChainId::Mainnet => SN_MAIN_STR,
            ChainId::Sepolia => SN_SEPOLIA_STR,
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[cfg(feature = "devnet")]
pub struct TryChainIdFromStringError(crate::short_string::TryShortStringFromStringError);

#[derive(Debug, Clone)]
#[cfg(not(feature = "devnet"))]
pub struct TryChainIdFromStringError(String);

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
        if value == SN_MAIN_STR {
            return Ok(ChainId::Mainnet);
        } else if value == SN_SEPOLIA_STR {
            return Ok(ChainId::Sepolia);
        }

        #[cfg(feature = "devnet")]
        match ShortString::try_from(value) {
            Ok(ss) => Ok(ChainId::Devnet(ss)),
            Err(e) => Err(TryChainIdFromStringError(e)),
        }

        #[cfg(not(feature = "devnet"))]
        Err(TryChainIdFromStringError(value))
    }
}

impl TryFrom<&str> for ChainId {
    type Error = TryChainIdFromStringError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if value == SN_MAIN_STR {
            return Ok(ChainId::Mainnet);
        } else if value == SN_SEPOLIA_STR {
            return Ok(ChainId::Sepolia);
        }

        #[cfg(feature = "devnet")]
        match ShortString::try_from(value) {
            Ok(ss) => Ok(ChainId::Devnet(ss)),
            Err(e) => Err(TryChainIdFromStringError(e)),
        }

        #[cfg(not(feature = "devnet"))]
        Err(TryChainIdFromStringError(value.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        chain_id::{SN_MAIN_STR, SN_SEPOLIA_STR},
        felt::Felt,
        short_string,
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
            let felt = Felt::from_hex_unchecked("0x63616665");
            let chain_id = ChainId::try_from(felt).unwrap();
            assert_eq!(Felt::from(chain_id), felt);

            // Non ascii
            let felt = Felt::from_hex_unchecked("0x1234567890");
            assert!(ChainId::try_from(felt).is_err());
            // Non too long
            let felt = Felt::from_hex_unchecked(
                "0x6363636363636363636363636363636363636363636363636363636363636363",
            );
            assert!(ChainId::try_from(felt).is_err());
        }
    }

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

    #[test]
    fn str_and_chain_id_round_trip() {
        let s = SN_MAIN_STR;
        let chain_id = ChainId::try_from(s).unwrap();
        assert_eq!(chain_id.to_string(), s.to_string());

        let s = SN_SEPOLIA_STR;
        let chain_id = ChainId::try_from(s).unwrap();
        assert_eq!(chain_id.to_string(), s.to_string());

        #[cfg(not(feature = "devnet"))]
        {
            let s = "SN_DEVNET";
            assert!(ChainId::try_from(s).is_err());
        }
        #[cfg(feature = "devnet")]
        {
            let s = "SN_DEVNET";
            let chain_id = ChainId::try_from(s).unwrap();
            assert_eq!(s, chain_id.to_string());
            let s = "SN_DEVNET_LOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOONG";
            assert!(ChainId::try_from(s).is_err());
            let s = "SN_DEVNET_🌟";
            assert!(ChainId::try_from(s).is_err());
        }
    }
}
