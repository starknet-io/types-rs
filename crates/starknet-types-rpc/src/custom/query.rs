// query offset:
//     0x0000000000000000000000000000000100000000000000000000000000000000

use serde::{Deserialize, Serialize};

use crate::{
    BroadcastedDeclareTxnV1, BroadcastedDeclareTxnV2, BroadcastedDeclareTxnV3, DeployAccountTxnV1,
    DeployAccountTxnV3, InvokeTxnV0, InvokeTxnV1, InvokeTxnV3,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
#[serde(tag = "version")]
pub enum BroadcastedDeclareTxn<F: Default> {
    #[serde(rename = "0x1")]
    V1(BroadcastedDeclareTxnV1<F>),
    #[serde(rename = "0x2")]
    V2(BroadcastedDeclareTxnV2<F>),
    #[serde(rename = "0x3")]
    V3(BroadcastedDeclareTxnV3<F>),
    /// Query-only broadcasted declare transaction.
    #[serde(rename = "0x0000000000000000000000000000000100000000000000000000000000000001")]
    QueryV1(BroadcastedDeclareTxnV1<F>),
    /// Query-only broadcasted declare transaction.
    #[serde(rename = "0x0000000000000000000000000000000100000000000000000000000000000002")]
    QueryV2(BroadcastedDeclareTxnV2<F>),
    /// Query-only broadcasted declare transaction.
    #[serde(rename = "0x0000000000000000000000000000000100000000000000000000000000000003")]
    QueryV3(BroadcastedDeclareTxnV3<F>),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
#[serde(tag = "version")]
pub enum BroadcastedDeployAccountTxn<F> {
    #[serde(rename = "0x1")]
    V1(DeployAccountTxnV1<F>),
    /// Query-only broadcasted deploy account transaction.
    #[serde(rename = "0x0000000000000000000000000000000100000000000000000000000000000001")]
    QueryV1(DeployAccountTxnV1<F>),
    /// Query-only broadcasted deploy account transaction.
    #[serde(rename = "0x0000000000000000000000000000000100000000000000000000000000000003")]
    QueryV3(DeployAccountTxnV3<F>),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
#[serde(tag = "version")]
pub enum BroadcastedInvokeTxn<F> {
    #[serde(rename = "0x0")]
    V0(InvokeTxnV0<F>),
    #[serde(rename = "0x1")]
    V1(InvokeTxnV1<F>),
    #[serde(rename = "0x3")]
    V3(InvokeTxnV3<F>),

    /// Query-only broadcasted invoke transaction.
    #[serde(rename = "0x0000000000000000000000000000000100000000000000000000000000000000")]
    QueryV0(InvokeTxnV0<F>),
    /// Query-only broadcasted invoke transaction.
    #[serde(rename = "0x0000000000000000000000000000000100000000000000000000000000000001")]
    QueryV1(InvokeTxnV1<F>),
    /// Query-only broadcasted invoke transaction.
    #[serde(rename = "0x0000000000000000000000000000000100000000000000000000000000000003")]
    QueryV3(InvokeTxnV3<F>),
}
