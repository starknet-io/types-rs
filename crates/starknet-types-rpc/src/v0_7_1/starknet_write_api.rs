//
// This file was automatically generated by openrpc-gen.
//
// Do not edit it manually and instead edit either the source OpenRPC document,
// the configuration file, or open an issue or pull request on the openrpc-gen
// GitHub repository.
//
//     https://github.com/nils-mathieu/openrpc-gen
//

use super::{BroadcastedDeclareTxn, BroadcastedDeployAccountTxn, BroadcastedInvokeTxn, TxnHash};
use core::marker::PhantomData;
use serde::ser::SerializeMap;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct ClassAndTxnHash<F> {
    pub class_hash: F,
    pub transaction_hash: TxnHash<F>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct ContractAndTxnHash<F> {
    pub contract_address: F,
    pub transaction_hash: TxnHash<F>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct AddInvokeTransactionResult<F> {
    pub transaction_hash: TxnHash<F>,
}

/// Parameters of the `starknet_addInvokeTransaction` method.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AddInvokeTransactionParams<F: Default> {
    /// The information needed to invoke the function (or account, for version 1 transactions)
    pub invoke_transaction: BroadcastedInvokeTxn<F>,
}

impl<F: Default + Serialize> Serialize for AddInvokeTransactionParams<F> {
    #[allow(unused_mut)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("invoke_transaction", &self.invoke_transaction)?;
        map.end()
    }
}

impl<'de, F: Default + Deserialize<'de>> Deserialize<'de> for AddInvokeTransactionParams<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct Visitor<F> {
            marker: PhantomData<F>,
        }

        impl<'de, F: Default + Deserialize<'de>> serde::de::Visitor<'de> for Visitor<F> {
            type Value = AddInvokeTransactionParams<F>;

            fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(f, "the parameters for `starknet_addInvokeTransaction`")
            }

            #[allow(unused_mut)]
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let invoke_transaction: BroadcastedInvokeTxn<F> = seq
                    .next_element()?
                    .ok_or_else(|| serde::de::Error::invalid_length(1, &"expected 1 parameters"))?;

                if seq.next_element::<serde::de::IgnoredAny>()?.is_some() {
                    return Err(serde::de::Error::invalid_length(
                        2,
                        &"expected 1 parameters",
                    ));
                }

                Ok(AddInvokeTransactionParams { invoke_transaction })
            }

            #[allow(unused_variables)]
            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                #[derive(Deserialize)]
                struct Helper<F: Default> {
                    invoke_transaction: BroadcastedInvokeTxn<F>,
                }

                let helper =
                    Helper::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;

                Ok(AddInvokeTransactionParams {
                    invoke_transaction: helper.invoke_transaction,
                })
            }
        }

        deserializer.deserialize_any(Visitor::<F> {
            marker: PhantomData,
        })
    }
}

/// Parameters of the `starknet_addDeclareTransaction` method.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AddDeclareTransactionParams<F: Default> {
    /// Declare transaction required to declare a new class on Starknet
    pub declare_transaction: BroadcastedDeclareTxn<F>,
}

impl<F: Default + Serialize> Serialize for AddDeclareTransactionParams<F> {
    #[allow(unused_mut)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("declare_transaction", &self.declare_transaction)?;
        map.end()
    }
}

impl<'de, F: Default + Deserialize<'de>> Deserialize<'de> for AddDeclareTransactionParams<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct Visitor<F> {
            marker: PhantomData<F>,
        }

        impl<'de, F: Default + Deserialize<'de>> serde::de::Visitor<'de> for Visitor<F> {
            type Value = AddDeclareTransactionParams<F>;

            fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(f, "the parameters for `starknet_addDeclareTransaction`")
            }

            #[allow(unused_mut)]
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let declare_transaction: BroadcastedDeclareTxn<F> = seq
                    .next_element()?
                    .ok_or_else(|| serde::de::Error::invalid_length(1, &"expected 1 parameters"))?;

                if seq.next_element::<serde::de::IgnoredAny>()?.is_some() {
                    return Err(serde::de::Error::invalid_length(
                        2,
                        &"expected 1 parameters",
                    ));
                }

                Ok(AddDeclareTransactionParams {
                    declare_transaction,
                })
            }

            #[allow(unused_variables)]
            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                #[derive(Deserialize)]
                struct Helper<F: Default> {
                    declare_transaction: BroadcastedDeclareTxn<F>,
                }

                let helper =
                    Helper::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;

                Ok(AddDeclareTransactionParams {
                    declare_transaction: helper.declare_transaction,
                })
            }
        }

        deserializer.deserialize_any(Visitor::<F> {
            marker: PhantomData,
        })
    }
}

/// Parameters of the `starknet_addDeployAccountTransaction` method.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AddDeployAccountTransactionParams<F> {
    /// The deploy account transaction
    pub deploy_account_transaction: BroadcastedDeployAccountTxn<F>,
}

impl<F: Serialize> Serialize for AddDeployAccountTransactionParams<F> {
    #[allow(unused_mut)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry(
            "deploy_account_transaction",
            &self.deploy_account_transaction,
        )?;
        map.end()
    }
}

impl<'de, F: Deserialize<'de>> Deserialize<'de> for AddDeployAccountTransactionParams<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct Visitor<F> {
            marker: PhantomData<F>,
        }

        impl<'de, F: Deserialize<'de>> serde::de::Visitor<'de> for Visitor<F> {
            type Value = AddDeployAccountTransactionParams<F>;

            fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(
                    f,
                    "the parameters for `starknet_addDeployAccountTransaction`"
                )
            }

            #[allow(unused_mut)]
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let deploy_account_transaction: BroadcastedDeployAccountTxn<F> = seq
                    .next_element()?
                    .ok_or_else(|| serde::de::Error::invalid_length(1, &"expected 1 parameters"))?;

                if seq.next_element::<serde::de::IgnoredAny>()?.is_some() {
                    return Err(serde::de::Error::invalid_length(
                        2,
                        &"expected 1 parameters",
                    ));
                }

                Ok(AddDeployAccountTransactionParams {
                    deploy_account_transaction,
                })
            }

            #[allow(unused_variables)]
            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                #[derive(Deserialize)]
                struct Helper<F> {
                    deploy_account_transaction: BroadcastedDeployAccountTxn<F>,
                }

                let helper =
                    Helper::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;

                Ok(AddDeployAccountTransactionParams {
                    deploy_account_transaction: helper.deploy_account_transaction,
                })
            }
        }

        deserializer.deserialize_any(Visitor::<F> {
            marker: PhantomData,
        })
    }
}
