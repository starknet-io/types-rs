//! Types used by the StarkNet RPC.

mod custom_serde;

#[path = "generated/v0_5_0.rs"]
mod generated;

pub use self::generated::*;

mod block_id;
mod syncing_status;

pub use self::block_id::*;
pub use self::syncing_status::*;
