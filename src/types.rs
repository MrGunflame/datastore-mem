use datastore::{Read, Reader, TypeWriter, Write, Writer};

use crate::MemStore;

impl Write<MemStore> for bool {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_bool(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_bool()
    }
}

impl Write<MemStore> for i8 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_i8(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_i8()
    }
}

impl Write<MemStore> for i16 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_i16(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_i16()
    }
}

impl Write<MemStore> for i32 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_i32(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_i32()
    }
}

impl Write<MemStore> for i64 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_i64(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_i64()
    }
}

impl Write<MemStore> for u8 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_u8(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_u8()
    }
}

impl Write<MemStore> for u16 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_u16(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_u16()
    }
}

impl Write<MemStore> for u32 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_u32(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_u32()
    }
}

impl Write<MemStore> for u64 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_u64(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_u64()
    }
}

impl Write<MemStore> for f32 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_f32(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_f32()
    }
}

impl Write<MemStore> for f64 {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_f64(*self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_f64()
    }
}

impl Write<MemStore> for [u8] {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_bytes(self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_bytes()
    }
}

impl Write<MemStore> for Vec<u8> {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_bytes(self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_bytes()
    }
}

impl Write<MemStore> for str {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_str(self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_str()
    }
}

impl Write<MemStore> for String {
    fn write<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: Writer<MemStore>,
    {
        writer.write_str(self)
    }

    fn write_type<W>(writer: &mut W) -> Result<(), W::Error>
    where
        W: TypeWriter<MemStore>,
    {
        writer.write_str()
    }
}

impl Read<MemStore> for bool {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_bool()?)
    }
}

impl Read<MemStore> for i8 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_i8()?)
    }
}

impl Read<MemStore> for i16 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_i16()?)
    }
}

impl Read<MemStore> for i32 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_i32()?)
    }
}

impl Read<MemStore> for i64 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_i64()?)
    }
}

impl Read<MemStore> for u8 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_u8()?)
    }
}

impl Read<MemStore> for u16 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_u16()?)
    }
}

impl Read<MemStore> for u32 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_u32()?)
    }
}

impl Read<MemStore> for u64 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_u64()?)
    }
}

impl Read<MemStore> for f32 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_f32()?)
    }
}

impl Read<MemStore> for f64 {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_f64()?)
    }
}

impl Read<MemStore> for Vec<u8> {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_byte_buf()?)
    }
}

impl Read<MemStore> for String {
    fn read<R>(reader: &mut R) -> Result<Self, R::Error>
    where
        R: Reader<MemStore>,
    {
        Ok(reader.read_string()?)
    }
}
