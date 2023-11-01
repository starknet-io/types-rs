//! Integeration tests for the 0.5.0 version of the StarkNet RPC API Specification.

use starknet_types_rpc::{BlockId, BlockTag, Felt, SyncingStatus};

#[test]
fn block_id_from_hash() {
    let s = "{\"block_hash\":\"0x123\"}";
    let block_id: BlockId = serde_json::from_str(s).unwrap();
    assert_eq!(block_id, BlockId::Hash(Felt::from_hex("0x123").unwrap()));
}

#[test]
fn block_id_from_number() {
    let s = "{\"block_number\":123}";
    let block_id: BlockId = serde_json::from_str(s).unwrap();
    assert_eq!(block_id, BlockId::Number(123));
}

#[test]
fn block_id_from_latest() {
    let s = "\"latest\"";
    let block_id: BlockId = serde_json::from_str(s).unwrap();
    assert_eq!(block_id, BlockId::Tag(BlockTag::Latest));
}

#[test]
fn block_id_from_pending() {
    let s = "\"pending\"";
    let block_id: BlockId = serde_json::from_str(s).unwrap();
    assert_eq!(block_id, BlockId::Tag(BlockTag::Pending));
}

#[test]
fn block_id_to_hash() {
    let block_id = BlockId::Hash(Felt::from_hex("0x123").unwrap());
    let s = serde_json::to_string(&block_id).unwrap();
    assert_eq!(s, "{\"block_hash\":\"0x123\"}");
}

#[test]
fn block_id_to_number() {
    let block_id = BlockId::Number(123);
    let s = serde_json::to_string(&block_id).unwrap();
    assert_eq!(s, "{\"block_number\":123}");
}

#[test]
fn block_id_to_latest() {
    let block_id = BlockId::Tag(BlockTag::Latest);
    let s = serde_json::to_string(&block_id).unwrap();
    assert_eq!(s, "\"latest\"");
}

#[test]
fn block_id_to_pending() {
    let block_id = BlockId::Tag(BlockTag::Pending);
    let s = serde_json::to_string(&block_id).unwrap();
    assert_eq!(s, "\"pending\"");
}

#[test]
fn syncing_status_from_false() {
    let s = "false";
    let syncing_status: SyncingStatus = serde_json::from_str(s).unwrap();
    assert!(matches!(syncing_status, SyncingStatus::NotSyncing));
}

#[test]
fn syncing_status_to_false() {
    let syncing_status = SyncingStatus::NotSyncing;
    let s = serde_json::to_string(&syncing_status).unwrap();
    assert_eq!(s, "false");
}

#[test]
fn syncing_status_from_true() {
    let s = "true";
    assert!(serde_json::from_str::<SyncingStatus>(s).is_err());
}
