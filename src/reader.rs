use std::mem;
use std::{collections::HashMap, convert::Infallible};

use datastore::{Read, Reader};

use crate::entries::Entry;
use crate::{DataKind, Error, MemStore};

pub struct MemReader<'a> {
    buf: &'a [u8],
    key: &'static str,
}

impl<'a> MemReader<'a> {
    /// Creates a new `MemReader` reading from the given buffer.
    #[inline]
    pub fn new(buf: &'a [u8]) -> Self {
        Self { buf, key: "" }
    }

    fn read<T>(&mut self) -> Result<T, Infallible> {
        #[cfg(debug_assertions)]
        assert!(self.buf.len() >= mem::size_of::<T>());

        let ptr = self.buf.as_ptr() as *const T;

        unsafe {
            self.buf = self.buf.get_unchecked(mem::size_of::<T>()..);
        }

        unsafe { Ok(std::ptr::read_unaligned(ptr)) }
    }

    fn read_buf(&mut self) -> Result<Vec<u8>, Infallible> {
        let len = self.read()?;

        let mut buf = Vec::with_capacity(len);

        #[cfg(debug_assertions)]
        assert!(self.buf.len() >= len);

        // Copy bytes into the new buffer.
        unsafe {
            let content = self.buf.as_ptr();
            std::ptr::copy_nonoverlapping(content, buf.as_mut_ptr(), len);

            // Update the length.
            buf.set_len(len);
        }

        // Move the cursor forward.
        unsafe {
            self.buf = self.buf.get_unchecked(len..);
        }

        Ok(buf)
    }
}

impl<'a> Reader<MemStore> for MemReader<'a> {
    type Error = Infallible;

    fn read_bool(&mut self) -> Result<bool, Self::Error> {
        self.read()
    }

    fn read_i8(&mut self) -> Result<i8, Self::Error> {
        self.read()
    }

    fn read_i16(&mut self) -> Result<i16, Self::Error> {
        self.read()
    }

    fn read_i32(&mut self) -> Result<i32, Self::Error> {
        self.read()
    }

    fn read_i64(&mut self) -> Result<i64, Self::Error> {
        self.read()
    }

    fn read_u8(&mut self) -> Result<u8, Self::Error> {
        self.read()
    }

    fn read_u16(&mut self) -> Result<u16, Self::Error> {
        self.read()
    }

    fn read_u32(&mut self) -> Result<u32, Self::Error> {
        self.read()
    }

    fn read_u64(&mut self) -> Result<u64, Self::Error> {
        self.read()
    }

    fn read_f32(&mut self) -> Result<f32, Self::Error> {
        self.read()
    }

    fn read_f64(&mut self) -> Result<f64, Self::Error> {
        self.read()
    }

    fn read_byte_buf(&mut self) -> Result<Vec<u8>, Self::Error> {
        self.read_buf()
    }

    fn read_string(&mut self) -> Result<String, Self::Error> {
        self.read_byte_buf()
            .map(|bytes| unsafe { String::from_utf8_unchecked(bytes) })
    }

    fn read_field<T>(&mut self, key: &'static str) -> Result<T, Self::Error>
    where
        T: Sized + Read<MemStore>,
    {
        self.key = key;
        T::read(self)
    }
}

#[cfg(test)]
mod tests {
    use datastore::Reader;

    use super::MemReader;

    #[test]
    fn test_mem_reader() {
        let mut buf = Vec::new();
        // U8
        buf.extend([5]);
        // U16
        buf.extend(50_000_u16.to_ne_bytes());
        // Bytes
        buf.extend(3_usize.to_ne_bytes());
        buf.extend([b'A', b'B', b'C']);
        // Str
        buf.extend(5_usize.to_ne_bytes());
        buf.extend("Hello".as_bytes());

        let mut reader = MemReader::new(&buf);

        assert_eq!(reader.read_u8().unwrap(), 5);
        assert_eq!(reader.read_u16().unwrap(), 50_000);
        assert_eq!(reader.read_byte_buf().unwrap(), [b'A', b'B', b'C']);
        assert_eq!(reader.read_string().unwrap(), "Hello");
    }
}
