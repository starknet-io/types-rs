//
// This file was automatically generated by openrpc-gen.
//
// Do not edit it manually and instead edit either the source OpenRPC document,
// the configuration file, or open an issue or pull request on the openrpc-gen
// GitHub repository.
//
//     https://github.com/nils-mathieu/openrpc-gen
//

use super::{
    BlockId, BroadcastedTxn, ComputationResources, Event, ExecutionResources, FeeEstimate,
    FunctionCall, MsgToL1, StateDiff, TxnHash,
};
use alloc::string::String;
use alloc::vec::Vec;
use serde::ser::SerializeMap;
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

#[derive(Eq, Hash, PartialEq, Serialize, Deserialize, Clone, Debug)]
pub enum CallType {
    #[serde(rename = "CALL")]
    Regular,
    #[serde(rename = "DELEGATE")]
    Delegate,
    #[serde(rename = "LIBRARY_CALL")]
    LibraryCall,
}

#[derive(Eq, Hash, PartialEq, Serialize, Deserialize, Clone, Debug)]
pub enum EntryPointType {
    #[serde(rename = "CONSTRUCTOR")]
    Constructor,
    #[serde(rename = "EXTERNAL")]
    External,
    #[serde(rename = "L1_HANDLER")]
    L1Handler,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct FunctionInvocation<F> {
    #[serde(flatten)]
    pub function_call: FunctionCall<F>,
    pub call_type: CallType,
    /// The address of the invoking contract. 0 for the root invocation
    pub caller_address: F,
    /// The calls made by this invocation
    pub calls: Vec<NestedCall<F>>,
    /// The hash of the class being called
    pub class_hash: F,
    pub entry_point_type: EntryPointType,
    /// The events emitted in this invocation
    pub events: Vec<OrderedEvent<F>>,
    /// Resources consumed by the internal call. This is named execution_resources for legacy reasons
    pub execution_resources: ComputationResources,
    /// The messages sent by this invocation to L1
    pub messages: Vec<OrderedMessage<F>>,
    /// The value returned from the function invocation
    pub result: Vec<F>,
}

pub type NestedCall<F> = FunctionInvocation<F>;

/// an event alongside its order within the transaction
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct OrderedEvent<F> {
    /// the order of the event within the transaction
    #[serde(default)]
    pub order: Option<u64>,
    #[serde(flatten)]
    pub event: Event<F>,
}

/// a message alongside its order within the transaction
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct OrderedMessage<F> {
    /// the order of the message within the transaction
    #[serde(default)]
    pub order: Option<u64>,
    #[serde(flatten)]
    pub msg_to_l_1: MsgToL1<F>,
}

/// Flags that indicate how to simulate a given transaction. By default, the sequencer behavior is replicated locally (enough funds are expected to be in the account, and fee will be deducted from the balance before the simulation of the next transaction). To skip the fee charge, use the SKIP_FEE_CHARGE flag.
#[derive(Eq, Hash, PartialEq, Serialize, Deserialize, Clone, Debug)]
pub enum SimulationFlag {
    #[serde(rename = "SKIP_FEE_CHARGE")]
    FeeCharge,
    #[serde(rename = "SKIP_VALIDATE")]
    Validate,
}

#[derive(Eq, Hash, PartialEq, Serialize, Deserialize, Clone, Debug)]
#[serde(tag = "type")]
pub enum TransactionTrace<F: Default> {
    /// the execution trace of an invoke transaction
    #[serde(rename = "INVOKE")]
    Invoke(InvokeTransactionTrace<F>),
    /// the execution trace of a declare transaction
    #[serde(rename = "DECLARE")]
    Declare(DeclareTransactionTrace<F>),
    /// the execution trace of a deploy account transaction
    #[serde(rename = "DEPLOY_ACCOUNT")]
    DeployAccount(DeployAccountTransactionTrace<F>),
    /// the execution trace of an L1 handler transaction
    #[serde(rename = "L1_HANDLER")]
    L1Handler(L1HandlerTransactionTrace<F>),
}

/// the execution trace of an invoke transaction
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct InvokeTransactionTrace<F: Default> {
    /// the trace of the __execute__ call or constructor call, depending on the transaction type (none for declare transactions)
    pub execute_invocation: ExecuteInvocation<F>,
    /// the resources consumed by the transaction, includes both computation and data
    pub execution_resources: ExecutionResources,
    #[serde(default)]
    pub fee_transfer_invocation: Option<FunctionInvocation<F>>,
    /// the state diffs induced by the transaction
    #[serde(default)]
    pub state_diff: Option<StateDiff<F>>,
    #[serde(default)]
    pub validate_invocation: Option<FunctionInvocation<F>>,
}

/// the trace of the __execute__ call or constructor call, depending on the transaction type (none for declare transactions)
#[derive(Eq, Hash, PartialEq, Serialize, Deserialize, Clone, Debug)]
#[serde(untagged)]
pub enum ExecuteInvocation<F> {
    FunctionInvocation(FunctionInvocation<F>),
    Anon(RevertedInvocation),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct RevertedInvocation {
    /// the revert reason for the failed execution
    pub revert_reason: String,
}

/// the execution trace of a declare transaction
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct DeclareTransactionTrace<F: Default> {
    /// the resources consumed by the transaction, includes both computation and data
    pub execution_resources: ExecutionResources,
    #[serde(default)]
    pub fee_transfer_invocation: Option<FunctionInvocation<F>>,
    /// the state diffs induced by the transaction
    #[serde(default)]
    pub state_diff: Option<StateDiff<F>>,
    #[serde(default)]
    pub validate_invocation: Option<FunctionInvocation<F>>,
}

/// the execution trace of a deploy account transaction
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct DeployAccountTransactionTrace<F: Default> {
    /// the trace of the __execute__ call or constructor call, depending on the transaction type (none for declare transactions)
    pub constructor_invocation: FunctionInvocation<F>,
    /// the resources consumed by the transaction, includes both computation and data
    pub execution_resources: ExecutionResources,
    #[serde(default)]
    pub fee_transfer_invocation: Option<FunctionInvocation<F>>,
    /// the state diffs induced by the transaction
    #[serde(default)]
    pub state_diff: Option<StateDiff<F>>,
    #[serde(default)]
    pub validate_invocation: Option<FunctionInvocation<F>>,
}

/// the execution trace of an L1 handler transaction
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct L1HandlerTransactionTrace<F: Default> {
    /// the resources consumed by the transaction, includes both computation and data
    pub execution_resources: ExecutionResources,
    /// the trace of the __execute__ call or constructor call, depending on the transaction type (none for declare transactions)
    pub function_invocation: FunctionInvocation<F>,
    /// the state diffs induced by the transaction
    #[serde(default)]
    pub state_diff: Option<StateDiff<F>>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct SimulateTransactionsResult<F: Default> {
    #[serde(default)]
    pub fee_estimation: Option<FeeEstimate<F>>,
    #[serde(default)]
    pub transaction_trace: Option<TransactionTrace<F>>,
}

/// A single pair of transaction hash and corresponding trace
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct TraceBlockTransactionsResult<F: Default> {
    #[serde(default)]
    pub trace_root: Option<TransactionTrace<F>>,
    #[serde(default)]
    pub transaction_hash: Option<F>,
}

/// Parameters of the `starknet_traceTransaction` method.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraceTransactionParams<F> {
    /// The hash of the transaction to trace
    pub transaction_hash: TxnHash<F>,
}

impl<F: Serialize> Serialize for TraceTransactionParams<F> {
    #[allow(unused_mut)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("transaction_hash", &self.transaction_hash)?;
        map.end()
    }
}

impl<'de, F: Deserialize<'de>> Deserialize<'de> for TraceTransactionParams<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct Visitor<F> {
            marker: PhantomData<F>,
        }

        impl<'de, F: Deserialize<'de>> serde::de::Visitor<'de> for Visitor<F> {
            type Value = TraceTransactionParams<F>;

            fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(f, "the parameters for `starknet_traceTransaction`")
            }

            #[allow(unused_mut)]
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let transaction_hash: TxnHash<F> = seq
                    .next_element()?
                    .ok_or_else(|| serde::de::Error::invalid_length(1, &"expected 1 parameters"))?;

                if seq.next_element::<serde::de::IgnoredAny>()?.is_some() {
                    return Err(serde::de::Error::invalid_length(
                        2,
                        &"expected 1 parameters",
                    ));
                }

                Ok(TraceTransactionParams { transaction_hash })
            }

            #[allow(unused_variables)]
            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                #[derive(Deserialize)]
                struct Helper<F> {
                    transaction_hash: TxnHash<F>,
                }

                let helper =
                    Helper::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;

                Ok(TraceTransactionParams {
                    transaction_hash: helper.transaction_hash,
                })
            }
        }

        deserializer.deserialize_any(Visitor::<F> {
            marker: PhantomData,
        })
    }
}

/// Parameters of the `starknet_simulateTransactions` method.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SimulateTransactionsParams<F: Default> {
    /// The hash of the requested block, or number (height) of the requested block, or a block tag, for the block referencing the state or call the transaction on.
    pub block_id: BlockId<F>,
    /// The transactions to simulate
    pub transactions: Vec<BroadcastedTxn<F>>,
    /// describes what parts of the transaction should be executed
    pub simulation_flags: Vec<SimulationFlag>,
}

impl<F: Default + Serialize> Serialize for SimulateTransactionsParams<F> {
    #[allow(unused_mut)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("block_id", &self.block_id)?;
        map.serialize_entry("transactions", &self.transactions)?;
        map.serialize_entry("simulation_flags", &self.simulation_flags)?;
        map.end()
    }
}

impl<'de, F: Default + Deserialize<'de>> Deserialize<'de> for SimulateTransactionsParams<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct Visitor<F> {
            marker: PhantomData<F>,
        }

        impl<'de, F: Default + Deserialize<'de>> serde::de::Visitor<'de> for Visitor<F> {
            type Value = SimulateTransactionsParams<F>;

            fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(f, "the parameters for `starknet_simulateTransactions`")
            }

            #[allow(unused_mut)]
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let block_id: BlockId<F> = seq
                    .next_element()?
                    .ok_or_else(|| serde::de::Error::invalid_length(1, &"expected 3 parameters"))?;
                let transactions: Vec<BroadcastedTxn<F>> = seq
                    .next_element()?
                    .ok_or_else(|| serde::de::Error::invalid_length(2, &"expected 3 parameters"))?;
                let simulation_flags: Vec<SimulationFlag> = seq
                    .next_element()?
                    .ok_or_else(|| serde::de::Error::invalid_length(3, &"expected 3 parameters"))?;

                if seq.next_element::<serde::de::IgnoredAny>()?.is_some() {
                    return Err(serde::de::Error::invalid_length(
                        4,
                        &"expected 3 parameters",
                    ));
                }

                Ok(SimulateTransactionsParams {
                    block_id,
                    transactions,
                    simulation_flags,
                })
            }

            #[allow(unused_variables)]
            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                #[derive(Deserialize)]
                struct Helper<F: Default> {
                    block_id: BlockId<F>,
                    transactions: Vec<BroadcastedTxn<F>>,
                    simulation_flags: Vec<SimulationFlag>,
                }

                let helper =
                    Helper::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;

                Ok(SimulateTransactionsParams {
                    block_id: helper.block_id,
                    transactions: helper.transactions,
                    simulation_flags: helper.simulation_flags,
                })
            }
        }

        deserializer.deserialize_any(Visitor::<F> {
            marker: PhantomData,
        })
    }
}

/// Parameters of the `starknet_traceBlockTransactions` method.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraceBlockTransactionsParams<F> {
    /// The hash of the requested block, or number (height) of the requested block, or a block tag
    pub block_id: BlockId<F>,
}

impl<F: Serialize> Serialize for TraceBlockTransactionsParams<F> {
    #[allow(unused_mut)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("block_id", &self.block_id)?;
        map.end()
    }
}

impl<'de, F: Deserialize<'de>> Deserialize<'de> for TraceBlockTransactionsParams<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct Visitor<F> {
            marker: PhantomData<F>,
        }

        impl<'de, F: Deserialize<'de>> serde::de::Visitor<'de> for Visitor<F> {
            type Value = TraceBlockTransactionsParams<F>;

            fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(f, "the parameters for `starknet_traceBlockTransactions`")
            }

            #[allow(unused_mut)]
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let block_id: BlockId<F> = seq
                    .next_element()?
                    .ok_or_else(|| serde::de::Error::invalid_length(1, &"expected 1 parameters"))?;

                if seq.next_element::<serde::de::IgnoredAny>()?.is_some() {
                    return Err(serde::de::Error::invalid_length(
                        2,
                        &"expected 1 parameters",
                    ));
                }

                Ok(TraceBlockTransactionsParams { block_id })
            }

            #[allow(unused_variables)]
            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                #[derive(Deserialize)]
                struct Helper<F> {
                    block_id: BlockId<F>,
                }

                let helper =
                    Helper::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;

                Ok(TraceBlockTransactionsParams {
                    block_id: helper.block_id,
                })
            }
        }

        deserializer.deserialize_any(Visitor::<F> {
            marker: PhantomData,
        })
    }
}
