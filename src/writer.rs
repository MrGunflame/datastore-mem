use std::{collections::HashMap, convert::Infallible};

use datastore::{Write, Writer};

use crate::{entries::Entry, MemStore};

#[derive(Debug)]
pub(crate) struct MemWriter {
    buf: Vec<u8>,
    fields: HashMap<String, usize>,
}

impl MemWriter {
    pub(crate) fn new() -> Self {
        Self {
            buf: Vec::new(),
            fields: HashMap::new(),
        }
    }

    pub(crate) fn into_entry(self) -> Entry {
        Entry {
            buf: self.buf,
            fields: self.fields,
        }
    }

    fn write(&mut self, v: &[u8]) -> Result<(), Infallible> {
        self.buf.extend(v);
        Ok(())
    }

    fn write_buf(&mut self, v: &[u8]) -> Result<(), Infallible> {
        self.buf.extend(v.len().to_ne_bytes());
        self.buf.extend(v);
        Ok(())
    }
}

impl Writer<MemStore> for MemWriter {
    type Error = Infallible;

    fn write_bool(&mut self, v: bool) -> Result<(), Self::Error> {
        self.write(&[v as u8])
    }

    fn write_i8(&mut self, v: i8) -> Result<(), Self::Error> {
        self.write(&[v as u8])
    }

    fn write_i16(&mut self, v: i16) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_i32(&mut self, v: i32) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_i64(&mut self, v: i64) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_u8(&mut self, v: u8) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_u16(&mut self, v: u16) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_u32(&mut self, v: u32) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_u64(&mut self, v: u64) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_f32(&mut self, v: f32) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_f64(&mut self, v: f64) -> Result<(), Self::Error> {
        self.write(&v.to_ne_bytes())
    }

    fn write_bytes(&mut self, v: &[u8]) -> Result<(), Self::Error> {
        self.write_buf(v)
    }

    fn write_str(&mut self, v: &str) -> Result<(), Self::Error> {
        self.write_buf(v.as_bytes())
    }

    fn write_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Write<MemStore>,
    {
        self.fields.insert(key.to_owned(), self.buf.len());
        value.write(self)
    }
}

#[cfg(test)]
mod tests {
    use datastore::Writer;

    use super::MemWriter;

    #[test]
    fn test_mem_writer() {
        let mut writer = MemWriter::new();
        let mut buf = Vec::new();

        writer.write_u8(5).unwrap();
        buf.extend([5]);
        assert_eq!(writer.buf, buf);

        writer.write_u16(50_000).unwrap();
        buf.extend(50_000_u16.to_ne_bytes());
        assert_eq!(writer.buf, buf);

        writer.write_bytes(&[b'A', b'B', b'C']).unwrap();
        buf.extend(3_usize.to_ne_bytes());
        buf.extend([b'A', b'B', b'C']);
        assert_eq!(writer.buf, buf);

        writer.write_str("Hello").unwrap();
        buf.extend(5_usize.to_ne_bytes());
        buf.extend([b'H', b'e', b'l', b'l', b'o']);
        assert_eq!(writer.buf, buf);
    }
}
