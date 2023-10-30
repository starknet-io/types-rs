use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::SyncStatus;

/// The syncing status of a node.
#[derive(Clone, Debug)]
pub enum SyncingStatus {
    /// The node is not syncing.
    NotSyncing,
    /// The node is syncing.
    Syncing(SyncStatus),
}

impl Serialize for SyncingStatus {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            SyncingStatus::NotSyncing => serializer.serialize_bool(false),
            SyncingStatus::Syncing(status) => status.serialize(serializer),
        }
    }
}

impl<'de> Deserialize<'de> for SyncingStatus {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct SyncingStatusVisitor;

        impl<'de> Visitor<'de> for SyncingStatusVisitor {
            type Value = SyncingStatus;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                writeln!(formatter, "a syncing status")
            }

            fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                if v {
                    Err(serde::de::Error::custom("expected a syncing status"))
                } else {
                    Ok(SyncingStatus::NotSyncing)
                }
            }

            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let status =
                    SyncStatus::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;

                Ok(SyncingStatus::Syncing(status))
            }
        }

        deserializer.deserialize_any(SyncingStatusVisitor)
    }
}
