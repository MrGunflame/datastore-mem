use std::collections::HashMap;
use std::marker::PhantomData;

use datastore::{DataDescriptor, DataQuery, StoreData};

use crate::reader::MemReader;
use crate::utils::unwrap_infallible;
use crate::writer::MemWriter;
use crate::ErrorKind;
use crate::{schema::Schema, Error, MemStore};

#[derive(Debug)]
pub(crate) struct Entries {
    schema: Schema,
    entries: Vec<Entry>,
}

impl Entries {
    /// Creates a new `Entries` using the provided [`Schema`].
    pub(crate) fn new(schema: Schema) -> Self {
        Self {
            schema,
            entries: Vec::new(),
        }
    }

    pub fn read_all<T, D>(&self, descriptor: D) -> Result<Vec<T>, Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
    {
        if !self.schema.eq(&descriptor) {
            return Err(ErrorKind::MissmatchingSchema.into());
        }

        unsafe { Ok(self.read_all_unchecked()) }
    }

    pub fn insert<T, D>(&mut self, descriptor: D, data: T) -> Result<(), Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
    {
        if !self.schema.eq(&descriptor) {
            return Err(ErrorKind::MissmatchingSchema.into());
        }

        // SAFETY: Schemas are matching.
        unsafe { self.insert_unchecked(data) };
        Ok(())
    }

    pub fn filter<T, D, Q>(&self, descriptor: D, query: Q) -> Result<FilterIter<'_, T>, Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
        Q: DataQuery<T, MemStore>,
    {
        if !self.schema.eq(&descriptor) {
            return Err(ErrorKind::MissmatchingSchema.into());
        }

        unsafe { Ok(self.filter_unchecked(query)) }
    }

    pub fn retain<T, D, Q>(&mut self, descriptor: D, query: Q) -> Result<(), Error>
    where
        T: StoreData<MemStore>,
        D: DataDescriptor<T, MemStore>,
        Q: DataQuery<T, MemStore>,
    {
        if !self.schema.eq(&descriptor) {
            return Err(ErrorKind::MissmatchingSchema.into());
        }

        unsafe { self.retain_unchecked(query) };
        Ok(())
    }

    pub unsafe fn read_all_unchecked<T>(&self) -> Vec<T>
    where
        T: StoreData<MemStore>,
    {
        let mut buf = Vec::with_capacity(self.entries.len());

        for entry in &self.entries {
            unsafe {
                buf.push(entry.read_unchecked());
            }
        }

        buf
    }

    /// Inserts a new [`StoreData`] into the `Entries` without checking whether the schema of new
    /// the newly inserted value matches the currently defined schema for this type.
    ///
    /// # Safety
    ///
    /// This method does not validate the schema of the newly inserted value against the currently
    /// defined schema. Missmatching schemas will very likely lead to undefined behavoir down the
    /// line.
    pub unsafe fn insert_unchecked<T>(&mut self, data: T)
    where
        T: StoreData<MemStore>,
    {
        let mut writer = MemWriter::new();
        unwrap_infallible(data.write(&mut writer));

        self.entries.push(writer.into_entry());
    }

    /// Returns a new iterator over all entries matching `query` without checking whether the
    /// schema of `query` matches the currently defined schema for this type.
    ///
    /// # Safety
    ///
    /// This method does not validate the schema of the query against the currently defined schema.
    /// Missmatching schemas will very likely lead to undefined behavoir down the line.
    pub unsafe fn filter_unchecked<T, Q>(&self, query: Q) -> FilterIter<'_, T>
    where
        T: StoreData<MemStore>,
        Q: DataQuery<T, MemStore>,
    {
        let mut writer = MemWriter::new();
        unwrap_infallible(query.write(&mut writer));

        FilterIter::new(self, writer.into_entry())
    }

    pub unsafe fn retain_unchecked<T, Q>(&mut self, query: Q)
    where
        T: StoreData<MemStore>,
        Q: DataQuery<T, MemStore>,
    {
        let mut writer = MemWriter::new();
        unwrap_infallible(query.write(&mut writer));

        let filter = writer.into_entry();

        dbg!(&filter);

        self.entries.retain(|entry| {
            // SAFETY: The caller guarantees that the schema matches.
            unsafe { !entry.filter_unchecked(&self.schema, &filter) }
        });
    }
}

#[derive(Debug)]
pub(crate) struct Entry {
    pub buf: Vec<u8>,
    pub fields: HashMap<String, usize>,
}

impl Entry {
    pub fn read_field(&self, key: &str) -> Option<&[u8]> {
        let index = self.fields.get(key)?;

        #[cfg(debug_assertions)]
        let _ = &[*index..];

        unsafe { Some(self.buf.get_unchecked(*index..)) }
    }

    /// Reads `T` from this `Entry` without checking whether `T` has the same schema as `Entry`.
    ///
    /// # Safety
    ///
    /// This method does not validate the schema of `T` against the currently defined schema for
    /// `Entry`. Missmatching schemas will very likely lead to undefined behavoir down the line.
    pub unsafe fn read_unchecked<T>(&self) -> T
    where
        T: StoreData<MemStore>,
    {
        let mut reader = MemReader::new(&self.buf);
        unwrap_infallible(T::read(&mut reader))
    }

    pub unsafe fn filter_unchecked(&self, schema: &Schema, filter: &Self) -> bool {
        for (key, _) in &filter.fields {
            match self.fields.get(key) {
                Some(_) => {
                    // Get the type of `key` from the schema.
                    let kind = schema.fields.get(key).unwrap();

                    // SAFETY: The caller guarantees that the schema matches.
                    unsafe {
                        if kind.read_unchecked(self.read_field(key).unwrap())
                            != kind.read_unchecked(filter.read_field(key).unwrap())
                        {
                            return false;
                        }
                    }
                }
                None => return false,
            }
        }

        true
    }
}

#[derive(Debug)]
pub(crate) struct FilterIter<'a, T>
where
    T: StoreData<MemStore>,
{
    entries: &'a [Entry],
    schema: &'a Schema,
    filter: Entry,
    _marker: PhantomData<T>,
}

impl<'a, T> FilterIter<'a, T>
where
    T: StoreData<MemStore>,
{
    fn new(entries: &'a Entries, filter: Entry) -> Self {
        Self {
            entries: &entries.entries,
            schema: &entries.schema,
            filter,
            _marker: PhantomData,
        }
    }
}

impl<'a, T> Iterator for FilterIter<'a, T>
where
    T: StoreData<MemStore>,
{
    type Item = &'a Entry;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let entry = self.entries.first()?;

            unsafe {
                // Move cursor forward.
                // SAFETY: Since `entry` is currently at index 1, this range is always
                // valid.
                self.entries = self.entries.get_unchecked(1..);

                if entry.filter_unchecked(&self.schema, &self.filter) {
                    return Some(entry);
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.entries.len()))
    }
}
