use std::collections::HashMap;
use std::convert::Infallible;
use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

use async_trait::async_trait;
use datastore::{
    DataDescriptor, DataQuery, Read, Reader, Store, StoreData, TypeWriter, Write, Writer,
};
use parking_lot::RwLock;
use thiserror::Error;

#[derive(Clone, Debug)]
pub struct MemStore {
    inner: Arc<Inner>,
}

#[async_trait]
impl Store for MemStore {
    type Error = Error;
    type DataStore = Self;

    async fn connect(uri: &str) -> Result<Self, Self::Error> {
        Ok(Self {
            inner: Arc::new(Inner {
                map: RwLock::new(HashMap::new()),
            }),
        })
    }

    async fn create<T, D>(&self, descriptor: D) -> Result<(), Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send + Sync,
    {
        Ok(())
    }

    async fn delete<T, D, Q>(&self, descriptor: D, query: Q) -> Result<(), Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
        Q: DataQuery<T, Self> + Send,
    {
        unimplemented!()
    }

    async fn get<T, D, Q>(&self, descriptor: D, query: Q) -> Result<Vec<T>, Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
        Q: DataQuery<T, Self> + Send,
    {
        unimplemented!()
    }

    async fn get_all<T, D>(&self, descriptor: D) -> Result<Vec<T>, Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
    {
        unimplemented!()
    }

    async fn get_one<T, D, Q>(&self, descriptor: D, query: Q) -> Result<Option<T>, Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
        Q: DataQuery<T, Self> + Send,
    {
        unimplemented!()
    }

    async fn insert<T, D>(&self, descriptor: D, data: T) -> Result<(), Self::Error>
    where
        T: StoreData<Self> + Send + Sync + 'static,
        D: DataDescriptor<T, Self> + Send,
    {
        let mut writer = MemWriter::new();
        data.write(&mut writer);

        self.inner.insert(descriptor.ident(), writer.into_entry());
        Ok(())
    }
}

#[derive(Debug)]
struct Inner {
    map: RwLock<HashMap<String, Vec<Entry>>>,
}

impl Inner {
    fn insert(&self, name: &str, entry: Entry) {
        let mut inner = self.map.write();

        match inner.get_mut(name) {
            Some(entries) => entries.push(entry),
            None => {
                inner.insert(name.to_string(), vec![entry]);
            }
        }
    }
}

unsafe impl Send for Inner {}
unsafe impl Sync for Inner {}

#[derive(Debug)]
struct Entry {
    buf: Vec<u8>,
    fields: HashMap<String, (DataKind, usize)>,
}

impl Entry {
    fn read_field(&self, key: &str, kind: DataKind) -> Result<&[u8], Error> {
        match self.fields.get(key) {
            Some((k, index)) => {
                if *k != kind {
                    Err(Error::InvalidType {
                        expected: kind,
                        found: *k,
                    })
                } else {
                    // SAFETY: The index is guaranteed to be within bounds.
                    unsafe { Ok(self.buf.get_unchecked(*index..)) }
                }
            }
            None => Err(Error::UnknownKey(key.to_string())),
        }
    }
}

/// Types of supported types.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DataKind {
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

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("unknown key: {0}")]
    UnknownKey(String),
    #[error("invalid type: expected {expected}, found {found}")]
    InvalidType { expected: DataKind, found: DataKind },
    #[error("{0}")]
    Custom(String),
}

impl datastore::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: ToString,
    {
        Self::Custom(msg.to_string())
    }
}

#[derive(Debug)]
struct MemWriter {
    buf: Vec<u8>,
    fields: HashMap<String, (DataKind, usize)>,
    kind: DataKind,
}

impl MemWriter {
    fn new() -> Self {
        Self {
            buf: Vec::new(),
            fields: HashMap::new(),
            kind: DataKind::Bool,
        }
    }

    fn write(&mut self, buf: &[u8], kind: DataKind) -> Result<(), Infallible> {
        self.buf.extend(buf);
        self.kind = kind;
        Ok(())
    }

    fn into_entry(self) -> Entry {
        Entry {
            buf: self.buf,
            fields: self.fields,
        }
    }
}

impl Writer<MemStore> for MemWriter {
    type Error = Infallible;

    fn write_bool(&mut self, v: bool) -> Result<(), Self::Error> {
        self.write(&[v as u8], DataKind::Bool)
    }

    fn write_i8(&mut self, v: i8) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::I8)
    }

    fn write_i16(&mut self, v: i16) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::I16)
    }

    fn write_i32(&mut self, v: i32) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::I32)
    }

    fn write_i64(&mut self, v: i64) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::I64)
    }

    fn write_u8(&mut self, v: u8) -> Result<(), Self::Error> {
        self.write(&[v], DataKind::U8)
    }

    fn write_u16(&mut self, v: u16) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::U16)
    }

    fn write_u32(&mut self, v: u32) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::U32)
    }

    fn write_u64(&mut self, v: u64) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::U64)
    }

    fn write_f32(&mut self, v: f32) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::F32)
    }

    fn write_f64(&mut self, v: f64) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes(), DataKind::F64)
    }

    fn write_bytes(&mut self, v: &[u8]) -> Result<(), Self::Error> {
        self.write(v, DataKind::Bytes)
    }

    fn write_str(&mut self, v: &str) -> Result<(), Self::Error> {
        self.write(v.as_bytes(), DataKind::String)
    }

    fn write_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Write<MemStore>,
    {
        let index = self.buf.len();
        value.write(self)?;
        self.fields.insert(key.to_string(), (self.kind, index));
        Ok(())
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

#[derive(Debug)]
struct MemReader<'a> {
    entry: &'a Entry,
    key: &'static str,
}

impl<'a> MemReader<'a> {
    fn new(entry: &'a Entry) -> Self {
        Self { entry, key: "" }
    }

    fn read(&self, key: &str, kind: DataKind) -> Result<&[u8], Error> {
        self.entry.read_field(key, kind)
    }

    fn read_copy<T>(&self, key: &str, kind: DataKind) -> Result<T, Error> {
        let buf = self.read(key, kind)?;

        let ptr = buf.as_ptr() as *const T;

        unsafe { Ok(std::ptr::read_unaligned(ptr)) }
    }
}

impl<'a> Reader<MemStore> for MemReader<'a> {
    type Error = Error;

    fn read_bool(&mut self) -> Result<bool, Self::Error> {
        self.read_copy(self.key, DataKind::Bool)
    }

    fn read_i8(&mut self) -> Result<i8, Self::Error> {
        self.read_copy(self.key, DataKind::I8)
    }

    fn read_i16(&mut self) -> Result<i16, Self::Error> {
        self.read_copy(self.key, DataKind::I16)
    }

    fn read_i32(&mut self) -> Result<i32, Self::Error> {
        self.read_copy(self.key, DataKind::I32)
    }

    fn read_i64(&mut self) -> Result<i64, Self::Error> {
        self.read_copy(self.key, DataKind::I64)
    }

    fn read_u8(&mut self) -> Result<u8, Self::Error> {
        self.read_copy(self.key, DataKind::U8)
    }

    fn read_u16(&mut self) -> Result<u16, Self::Error> {
        self.read_copy(self.key, DataKind::U16)
    }

    fn read_u32(&mut self) -> Result<u32, Self::Error> {
        self.read_copy(self.key, DataKind::U32)
    }

    fn read_u64(&mut self) -> Result<u64, Self::Error> {
        self.read_copy(self.key, DataKind::U64)
    }

    fn read_f32(&mut self) -> Result<f32, Self::Error> {
        self.read_copy(self.key, DataKind::F32)
    }

    fn read_f64(&mut self) -> Result<f64, Self::Error> {
        self.read_copy(self.key, DataKind::F64)
    }

    fn read_byte_buf(&mut self) -> Result<Vec<u8>, Self::Error> {
        let buf = self.read(self.key, DataKind::Bytes)?;

        let ptr = buf.as_ptr() as *const usize;
        let len = unsafe { std::ptr::read_unaligned(ptr) };

        let mut bytes = Vec::with_capacity(len);

        let content = unsafe { buf.as_ptr().add(std::mem::size_of::<usize>()) };

        unsafe {
            std::ptr::copy(content, bytes.as_mut_ptr(), len);
        }

        Ok(bytes)
    }

    fn read_string(&mut self) -> Result<String, Self::Error> {
        let buf = self.read_byte_buf()?;

        unsafe { Ok(String::from_utf8_unchecked(buf)) }
    }

    fn read_field<T>(&mut self, key: &'static str) -> Result<T, Self::Error>
    where
        T: ?Sized + Read<MemStore>,
    {
        self.key = key;
        T::read(self)
    }
}
