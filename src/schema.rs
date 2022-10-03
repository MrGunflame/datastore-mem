//! Schema definitions for [`MemStore`].
//!
//! We need to predefine a schema to avoid collisions between different [`StoreData`] types that
//! have the same name. Due to how comparisons are handled in this crate, not doing this could
//! lead to an unsound API.
use std::collections::HashMap;

use datastore::{DataDescriptor, StoreData};

use crate::utils::unwrap_infallible;
use crate::{DataKind, MemStore, MemTypeWriter};

/// A schema describing the format of a specific type.
#[derive(Debug)]
pub(crate) struct Schema {
    pub fields: HashMap<String, DataKind>,
}

impl Schema {
    /// Creates a new `Schema` from a [`DataDescriptor`].
    pub(crate) fn from_descriptor<T, D>(descriptor: &D) -> Self
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
    {
        let mut writer = MemTypeWriter::new();

        unwrap_infallible(descriptor.write(&mut writer));

        let fields = writer.values.into_iter().collect();

        Self { fields }
    }

    /// Compares the schema with a [`DataDescriptor`] and returns `true` if they describe the same
    /// entry.
    pub(crate) fn eq<T, D>(&self, descriptor: &D) -> bool
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
    {
        let mut writer = MemTypeWriter::new();
        unwrap_infallible(descriptor.write(&mut writer));

        let mut fields = self.fields.clone();
        for (key, kind) in writer.values.into_iter() {
            match fields.remove(&key) {
                Some(k) => {
                    // Missmatching types on same key.
                    if kind != k {
                        return false;
                    }
                }
                // `descriptor` has a field that `self` doesn't have.
                None => return false,
            }
        }

        // If we have keys remaining, `descriptor` only partially describes `self`.
        fields.is_empty()
    }
}
