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

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod custom;
mod custom_serde;

//
// Generated files.
//
pub mod v0_5_0;

pub use self::v0_5_0::*;

use starknet_types_core::curve::ProjectivePoint;

fn double_operations() {
    let projective_point = ProjectivePoint::new(
        Felt::from_dec_str(
            "874739451078007766457464989774322083649278607533249481151382481072868806602",
        )
        .unwrap(),
        Felt::from_dec_str(
            "152666792071518830868575557812948353041420400780739481342941381225525861407",
        )
        .unwrap(),
        Felt::from(1),
    );
}
