//! A in-memory datastore Store implementation.
//!
//! This crate provides [`MemStore`], datastore [`Store`] implementation which keeps all entries
//! in memory. It is meant to be fast and efficient, making it a good backing store for in-memory
//! caches.
//!
//! ## Examples
//!
//! ```
//! use datastore::{Store, StoreExt, StoreData};
//! use datastore_mem::{Error, MemStore};
//!
//! #[derive(Clone, Debug, PartialEq, StoreData)]
//! struct Person {
//!     id: i64,
//!     name: String,
//! }
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Error> {
//!     let store = MemStore::connect("").await?;
//!
//!     let person = Person {
//!         id: 1,
//!         name: String::from("Robb"),
//!     };
//!
//!     Store::insert(&store, store.descriptor::<Person>(), person.clone()).await?;
//!
//!     let persons: Vec<Person> = Store::get_all(&store, store.descriptor::<Person>()).await?;
//!     assert_eq!(persons, [person]);
//!
//!     Ok(())
//! }
//! ```
//!
//! # Sync methods
//!
//! Since [`MemStore`] doesn't need to do any I/O it provides a set of synchronous methods in
//! addition to the asynchronous [`Store`] implementation.
//!
//! ## Examples
//!
//! ```
//! use datastore::{Store, StoreExt, StoreData};
//! use datastore_mem::{Error, MemStore};
//!
//! #[derive(Clone, Debug, PartialEq, StoreData)]
//! struct Person {
//!     id: i64,
//!     name: String,
//! }
//!
//! fn main() -> Result<(), Error> {
//!     let store = MemStore::new();
//!     
//!     let person = Person {
//!         id: 1,
//!         name: String::from("Robb"),
//!     };
//!
//!     store.insert(store.descriptor::<Person>(), person.clone())?;
//!
//!     let persons: Vec<Person> = store.get_all(store.descriptor::<Person>())?;
//!     assert_eq!(persons, [person]);
//!
//!     Ok(())
//! }
//! ```
//!
//! # Supported Types
//!
//! [`MemStore`] currently supports the following types:
//! - `bool`
//! - `i8`, `i16`, `i32`, `i64`
//! - `u8`, `u32`, `u32`, `u64`
//! - `f32`, `f64`
//! - `&str`, `String`
//! - `&[u8]`, `Vec<u8>`
//!
//! [`Store`]: datastore::Store
#![deny(unsafe_op_in_unsafe_fn)]

mod entries;
mod reader;
mod schema;
mod types;
mod utils;
mod writer;

use std::collections::HashMap;
use std::convert::Infallible;
use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

use async_trait::async_trait;
use datastore::{DataDescriptor, DataQuery, Store, StoreData, TypeWriter, Write};
use entries::Entries;
use parking_lot::RwLock;
use schema::Schema;
use thiserror::Error;

/// A in-memory store.
#[derive(Clone, Debug)]
pub struct MemStore {
    inner: Arc<Inner>,
}

impl MemStore {
    /// Creates a new, empty `MemStore`.
    pub fn new() -> Self {
        Self {
            inner: Arc::new(Inner {
                map: RwLock::new(HashMap::new()),
            }),
        }
    }

    /// Deletes all entries of `T` matching the query `Q`.
    #[inline]
    pub fn delete<T, D, Q>(&self, descriptor: D, query: Q) -> Result<(), Error>
    where
        T: StoreData<Self>,
        D: DataDescriptor<T, Self>,
        Q: DataQuery<T, Self>,
    {
        self.inner.delete(descriptor, query)
    }

    /// Returns all entries of `T` matching the query `Q`.
    #[inline]
    pub fn get<T, D, Q>(&self, descriptor: D, query: Q) -> Result<Vec<T>, Error>
    where
        T: StoreData<Self>,
        D: DataDescriptor<T, Self>,
        Q: DataQuery<T, Self>,
    {
        self.inner.get(descriptor, query)
    }

    /// Returns a list of all entries of `T`.
    #[inline]
    pub fn get_all<T, D>(&self, descriptor: D) -> Result<Vec<T>, Error>
    where
        T: StoreData<Self>,
        D: DataDescriptor<T, Self>,
    {
        self.inner.get_all(descriptor)
    }

    /// Returns the first inserted entry of `T` matching the query `Q`.
    #[inline]
    pub fn get_one<T, D, Q>(&self, descriptor: D, query: Q) -> Result<Option<T>, Error>
    where
        T: StoreData<Self>,
        D: DataDescriptor<T, Self>,
        Q: DataQuery<T, Self>,
    {
        self.inner.get_one(descriptor, query)
    }

    /// Inserts a new type `T` into the store.
    #[inline]
    pub fn insert<T, D>(&self, descriptor: D, data: T) -> Result<(), Error>
    where
        T: StoreData<Self>,
        D: DataDescriptor<T, Self>,
    {
        self.inner.insert(descriptor, data)
    }
}

#[async_trait]
impl Store for MemStore {
    type Error = Error;
    type DataStore = Self;

    async fn connect(_uri: &str) -> Result<Self, Self::Error> {
        Ok(Self {
            inner: Arc::new(Inner {
                map: RwLock::new(HashMap::new()),
            }),
        })
    }

    #[inline]
    async fn create<T, D>(&self, _descriptor: D) -> Result<(), Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send + Sync,
    {
        Ok(())
    }

    #[inline]
    async fn delete<T, D, Q>(&self, descriptor: D, query: Q) -> Result<(), Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
        Q: DataQuery<T, Self> + Send,
    {
        self.inner.delete(descriptor, query)
    }

    #[inline]
    async fn get<T, D, Q>(&self, descriptor: D, query: Q) -> Result<Vec<T>, Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
        Q: DataQuery<T, Self> + Send,
    {
        self.inner.get(descriptor, query)
    }

    #[inline]
    async fn get_all<T, D>(&self, descriptor: D) -> Result<Vec<T>, Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
    {
        self.inner.get_all(descriptor)
    }

    #[inline]
    async fn get_one<T, D, Q>(&self, descriptor: D, query: Q) -> Result<Option<T>, Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
        Q: DataQuery<T, Self> + Send,
    {
        self.inner.get_one(descriptor, query)
    }

    #[inline]
    async fn insert<T, D>(&self, descriptor: D, data: T) -> Result<(), Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
    {
        self.inner.insert(descriptor, data)
    }
}

#[derive(Debug)]
struct Inner {
    map: RwLock<HashMap<String, Entries>>,
}

impl Inner {
    fn insert<T, D>(&self, descriptor: D, data: T) -> Result<(), Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
    {
        let mut inner = self.map.write();

        match inner.get_mut(descriptor.ident()) {
            Some(entries) => entries.insert(descriptor, data),
            // Initialize the schema.
            None => {
                let schema = Schema::from_descriptor(&descriptor);
                let mut entries = Entries::new(schema);

                // SAFETY: We used `T` to create the schema, so the newly created `Entries`
                // is always valid for `T`.
                unsafe {
                    entries.insert_unchecked(data);
                }

                inner.insert(descriptor.ident().to_owned(), entries);
                Ok(())
            }
        }
    }

    fn delete<T, D, Q>(&self, descriptor: D, query: Q) -> Result<(), Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
        Q: DataQuery<T, MemStore>,
    {
        let mut inner = self.map.write();

        match inner.get_mut(descriptor.ident()) {
            Some(entries) => entries.retain(descriptor, query),
            None => Ok(()),
        }
    }

    fn get<T, D, Q>(&self, descriptor: D, query: Q) -> Result<Vec<T>, Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
        Q: DataQuery<T, MemStore>,
    {
        let inner = self.map.read();

        match inner.get(descriptor.ident()) {
            Some(entries) => {
                Ok(entries
                    .filter(descriptor, query)?
                    .map(|entry| {
                        // SAFETY: The call to `filter` already validates the schema.
                        unsafe { entry.read_unchecked() }
                    })
                    .collect())
            }
            None => Ok(Vec::new()),
        }
    }

    fn get_all<T, D>(&self, descriptor: D) -> Result<Vec<T>, Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
    {
        let inner = self.map.read();

        match inner.get(descriptor.ident()) {
            Some(entries) => entries.read_all(descriptor),
            None => Ok(Vec::new()),
        }
    }

    fn get_one<T, D, Q>(&self, descriptor: D, query: Q) -> Result<Option<T>, Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
        Q: DataQuery<T, MemStore>,
    {
        let inner = self.map.read();

        match inner.get(descriptor.ident()) {
            Some(entries) => Ok(entries
                .filter(descriptor, query)?
                .map(|entry| {
                    // SAFETY: The call to `filter` already validates the schema.
                    unsafe { entry.read_unchecked() }
                })
                .next()),
            None => Ok(None),
        }
    }
}

unsafe impl Send for Inner {}
unsafe impl Sync for Inner {}

/// Types of supported types.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum DataKind {
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bytes,
    String,
}

impl DataKind {
    /// Reads the buffer of the value of `self` from `buf` without checking if the buffer is big
    /// enough.
    ///
    /// # Safety
    ///
    /// Calling this method with a buffer that is not big enough to hold `self` causes undefined
    /// behavoir.
    unsafe fn read_unchecked<'a>(&self, buf: &'a [u8]) -> &'a [u8] {
        match self {
            Self::Bool | Self::I8 | Self::U8 => {
                #[cfg(debug_assertions)]
                let _ = &buf[..1];

                // SAFETY: The caller guarantees that the buffer is big enough.
                unsafe { buf.get_unchecked(..1) }
            }
            Self::I16 | Self::U16 => {
                #[cfg(debug_assertions)]
                let _ = &buf[..2];

                // SAFETY: The caller guarantees that the buffer is big enough.
                unsafe { buf.get_unchecked(..2) }
            }
            Self::I32 | Self::U32 | Self::F32 => {
                #[cfg(debug_assertions)]
                let _ = &buf[..4];

                // SAFETY: The caller guarantees that the buffer is big enough.
                unsafe { buf.get_unchecked(..4) }
            }
            Self::I64 | Self::U64 | Self::F64 => {
                #[cfg(debug_assertions)]
                let _ = &buf[..8];

                // SAFETY: The caller guarantees that the buffer is big enough.
                unsafe { buf.get_unchecked(..8) }
            }
            Self::Bytes | Self::String => {
                #[cfg(debug_assertions)]
                let _ = &buf[..std::mem::size_of::<usize>()];

                // Read the length from the buffer.
                let len = unsafe { std::ptr::read_unaligned(buf.as_ptr() as *const usize) };

                // Read the complete buffer including length.
                // SAFETY: The caller guarantees that the buffer is big enough.
                unsafe { buf.get_unchecked(..len) }
            }
        }
    }
}

impl Display for DataKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "bool"),
            Self::I8 => write!(f, "i8"),
            Self::I16 => write!(f, "i16"),
            Self::I32 => write!(f, "i32"),
            Self::I64 => write!(f, "i64"),
            Self::U8 => write!(f, "u8"),
            Self::U16 => write!(f, "u16"),
            Self::U32 => write!(f, "u32"),
            Self::U64 => write!(f, "u64"),
            Self::F32 => write!(f, "f32"),
            Self::F64 => write!(f, "f64"),
            Self::Bytes => write!(f, "[u8]"),
            Self::String => write!(f, "str"),
        }
    }
}

/// An error that can occur when using [`MemStore`].
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[error(transparent)]
pub struct Error(#[from] ErrorKind);

impl Error {
    /// Returns `true` if this error was created with [`Error::custom`].
    ///
    /// [`Error::custom`]: datastore::Error::custom
    #[inline]
    pub fn is_custom(&self) -> bool {
        matches!(self.0, ErrorKind::Custom(_))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
enum ErrorKind {
    #[error("{0}")]
    Custom(String),
    #[error("missmatching schema")]
    MissmatchingSchema,
}

impl datastore::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: ToString,
    {
        Self(ErrorKind::Custom(msg.to_string()))
    }
}

#[derive(Debug)]
struct MemTypeWriter {
    values: Vec<(String, DataKind)>,
    kind: DataKind,
}

impl MemTypeWriter {
    fn new() -> Self {
        Self {
            values: Vec::new(),
            kind: DataKind::Bool,
        }
    }
}

impl TypeWriter<MemStore> for MemTypeWriter {
    type Error = Infallible;

    fn write_bool(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::Bool;
        Ok(())
    }

    fn write_i8(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::I8;
        Ok(())
    }

    fn write_i16(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::I16;
        Ok(())
    }

    fn write_i32(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::I32;
        Ok(())
    }

    fn write_i64(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::I64;
        Ok(())
    }

    fn write_u8(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::U8;
        Ok(())
    }

    fn write_u16(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::U16;
        Ok(())
    }

    fn write_u32(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::U32;
        Ok(())
    }

    fn write_u64(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::U64;
        Ok(())
    }

    fn write_f32(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::F32;
        Ok(())
    }

    fn write_f64(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::F64;
        Ok(())
    }

    fn write_bytes(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::Bytes;
        Ok(())
    }

    fn write_str(&mut self) -> Result<(), Self::Error> {
        self.kind = DataKind::String;
        Ok(())
    }

    fn write_field<T>(&mut self, key: &'static str) -> Result<(), Self::Error>
    where
        T: Write<MemStore> + ?Sized,
    {
        T::write_type(self)?;

        self.values.push((key.to_string(), self.kind));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use datastore::StoreData;

    use crate::DataKind;

    use super::MemStore;

    #[test]
    fn test_data_kind_read_unchecked() {
        let buf = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            assert_eq!(DataKind::Bool.read_unchecked(&buf), [0]);
            assert_eq!(DataKind::I8.read_unchecked(&buf), [0]);
            assert_eq!(DataKind::U8.read_unchecked(&buf), [0]);

            assert_eq!(DataKind::I16.read_unchecked(&buf), [0, 1]);
            assert_eq!(DataKind::U16.read_unchecked(&buf), [0, 1]);

            assert_eq!(DataKind::I32.read_unchecked(&buf), [0, 1, 2, 3]);
            assert_eq!(DataKind::U32.read_unchecked(&buf), [0, 1, 2, 3]);

            assert_eq!(DataKind::I64.read_unchecked(&buf), [0, 1, 2, 3, 4, 5, 6, 7]);
            assert_eq!(DataKind::U64.read_unchecked(&buf), [0, 1, 2, 3, 4, 5, 6, 7]);
        }
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq, StoreData)]
    #[datastore(name = "test")]
    struct TestData {
        id: u8,
        name: String,
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq, StoreData)]
    #[datastore(name = "test")]
    struct Collide {
        x: u8,
    }

    #[tokio::test]
    async fn test_store() {
        let store = MemStore::new();

        let data = TestData::default();
        let descriptor = <TestData as StoreData<_>>::Descriptor::default();

        store.insert(descriptor, data.clone()).unwrap();

        let entries = store.get_all(descriptor).unwrap();
        assert_eq!(entries, [data.clone()]);

        let data2 = TestData {
            id: 128,
            name: "Hello World".into(),
        };

        store.insert(descriptor, data2.clone()).unwrap();

        let entries = store.get_all(descriptor).unwrap();
        assert_eq!(entries, [data.clone(), data2.clone()]);

        let entries = store
            .get(descriptor, TestDataQuery::default().id(128))
            .unwrap();
        assert_eq!(entries, [data2]);

        store
            .delete(
                descriptor,
                TestDataQuery::default().name("Hello World".into()),
            )
            .unwrap();

        let entry = store
            .get_one(descriptor, TestDataQuery::default().id(0))
            .unwrap();
        assert_eq!(entry, Some(data));
    }

    #[tokio::test]
    async fn test_store_collision() {
        let store = MemStore::new();

        let data = TestData::default();
        let descriptor = <TestData as StoreData<_>>::Descriptor::default();

        store.insert(descriptor, data).unwrap();

        let data = Collide::default();
        let descriptor = <Collide as StoreData<_>>::Descriptor::default();
        store.insert(descriptor, data).unwrap_err();
    }
}
