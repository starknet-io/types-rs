//! Types used by the [StarkNet RPC API Specification](spec).
//!
//! [spec]: https://github.com/starkware-libs/starknet-specs/blob/master/api/starknet_api_openrpc.json
//!
//! # Generation
//!
//! Most of the types of this crate are generated directly from the specification using
//! [openrpc-gen](https://github.com/nils-mathieu/openrpc-gen), ensuring that they are always
//! up-to-date.
//!
//! All generated types implement [`Clone`] and [`Debug`], as well as [`serde`]'s [`Serialize`]
//! and [`Deserialize`] to allow for easy serialization and deserialization.
//!
//! [`Serialize`]: serde::Serialize
//! [`Deserialize`]: serde::Deserialize

mod custom_serde;

#[path = "generated/v0_5_0.rs"]
mod generated;

pub use self::generated::*;

mod block_id;
mod syncing_status;

pub use self::block_id::*;
pub use self::syncing_status::*;
