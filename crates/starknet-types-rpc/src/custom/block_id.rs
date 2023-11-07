use serde::{Deserialize, Deserializer, Serialize};

use crate::{BlockHash, BlockNumber, BlockTag};

/// A hexadecimal number.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BlockId {
    /// The tag of the block.
    Tag(BlockTag),
    /// The hash of the block.
    Hash(BlockHash),
    /// The height of the block.
    Number(BlockNumber),
}

#[derive(Serialize, Deserialize)]
struct BlockHashHelper {
    block_hash: BlockHash,
}

#[derive(Serialize, Deserialize)]
struct BlockNumberHelper {
    block_number: BlockNumber,
}

#[derive(Deserialize)]
#[serde(untagged)]
enum BlockIdHelper {
    Tag(BlockTag),
    Hash(BlockHashHelper),
    Number(BlockNumberHelper),
}

impl serde::Serialize for BlockId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match *self {
            BlockId::Tag(tag) => tag.serialize(serializer),
            BlockId::Hash(block_hash) => {
                let helper = BlockHashHelper { block_hash };
                helper.serialize(serializer)
            }
            BlockId::Number(block_number) => {
                let helper = BlockNumberHelper { block_number };
                helper.serialize(serializer)
            }
        }
    }
}

impl<'de> serde::Deserialize<'de> for BlockId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let helper = BlockIdHelper::deserialize(deserializer)?;
        match helper {
            BlockIdHelper::Tag(tag) => Ok(BlockId::Tag(tag)),
            BlockIdHelper::Hash(helper) => Ok(BlockId::Hash(helper.block_hash)),
            BlockIdHelper::Number(helper) => Ok(BlockId::Number(helper.block_number)),
        }
    }
}
