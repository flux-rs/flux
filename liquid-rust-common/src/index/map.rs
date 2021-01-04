use crate::index::Index;

use std::{fmt, marker::PhantomData};

/// An associative array which uses an [Index] as key.
///
/// This is just a thin wrapper over a [Vec].
#[derive(Clone)]
pub struct IndexMap<K: Index, V> {
    inner: Vec<V>,
    marker: PhantomData<K>,
}

impl<K: Index, V> IndexMap<K, V> {
    /// Create a new, empty map.
    pub fn new() -> Self {
        Self {
            inner: Vec::new(),
            marker: PhantomData,
        }
    }

    /// Create a new, empty map and preallocate memory to store at most `capacity` elements without
    /// reallocations.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Vec::with_capacity(capacity),
            marker: PhantomData,
        }
    }

    /// Return the number of elements of the map.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Get the key that would be returned when calling `insert`.
    pub fn next_key(&self) -> K {
        K::new(self.len())
    }

    /// Insert a value and get the key that maps to it.
    pub fn insert(&mut self, value: V) -> K {
        let key = self.next_key();
        self.inner.push(value);
        key
    }

    /// Remove the last inserted value.
    pub fn remove(&mut self) -> Option<(K, V)> {
        let value = self.inner.pop()?;
        Some((self.next_key(), value))
    }

    /// Get an immutable reference to value using its key. Return `None` if the key does not map to
    /// any value.
    pub fn get(&self, key: K) -> Option<&V> {
        self.inner.get(key.index())
    }

    /// Get a mutable reference to value using its key. Return `None` if the key does not map to
    /// any value.
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.inner.get_mut(key.index())
    }

    /// Get an iterator over the keys and values (by reference) of the map.
    pub fn iter(&self) -> IndexIterRef<K, V> {
        IndexIterRef {
            iter: self.inner.as_slice().into_iter(),
            index: 0,
            index_back: self.inner.len(),
            marker: PhantomData,
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = K> {
        (0..self.len()).map(K::new)
    }

    /// Get an iterator over the keys and values (by mutable reference) of the map.
    pub fn iter_mut(&mut self) -> IndexIterMut<K, V> {
        IndexIterMut {
            iter: self.inner.as_mut_slice().into_iter(),
            index: 0,
            marker: PhantomData,
        }
    }

    /// Consume the map to return a `Vec`.
    ///
    /// The values are in insertion order.
    pub fn into_raw(self) -> Vec<V> {
        self.inner
    }

    /// Consume a `Vec` to produce a map.
    pub fn from_raw(inner: Vec<V>) -> Self {
        Self {
            inner,
            marker: PhantomData,
        }
    }
}

/// An iterator over the keys and values (by value) of a map.
pub struct IndexIter<K: Index, V> {
    iter: std::vec::IntoIter<V>,
    index: usize,
    marker: PhantomData<K>,
}

impl<K: Index, V> Iterator for IndexIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.iter.next()?;
        let key = K::new(self.index);
        self.index += 1;

        Some((key, value))
    }
}

/// An iterator over the keys and values (by reference) of a map.
pub struct IndexIterRef<'map, K: Index, V> {
    iter: std::slice::Iter<'map, V>,
    index: usize,
    index_back: usize,
    marker: PhantomData<K>,
}

impl<'map, K: Index, V> Iterator for IndexIterRef<'map, K, V> {
    type Item = (K, &'map V);

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.iter.next()?;
        let key = K::new(self.index);
        self.index += 1;

        Some((key, value))
    }
}

impl<'map, K: Index, V> DoubleEndedIterator for IndexIterRef<'map, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let value = self.iter.next_back()?;
        self.index_back -= 1;
        let key = K::new(self.index_back);

        Some((key, value))
    }
}

/// An iterator over the keys and values (by mutable reference) of a map.
pub struct IndexIterMut<'map, K: Index, V> {
    iter: std::slice::IterMut<'map, V>,
    index: usize,
    marker: PhantomData<K>,
}

impl<'map, K: Index, V> Iterator for IndexIterMut<'map, K, V> {
    type Item = (K, &'map V);

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.iter.next()?;
        let key = K::new(self.index);
        self.index += 1;

        Some((key, value))
    }
}

impl<K: Index, V> IntoIterator for IndexMap<K, V> {
    type Item = (K, V);
    type IntoIter = IndexIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IndexIter {
            iter: self.inner.into_iter(),
            index: 0,
            marker: PhantomData,
        }
    }
}

impl<'map, K: Index, V> IntoIterator for &'map IndexMap<K, V> {
    type Item = (K, &'map V);
    type IntoIter = IndexIterRef<'map, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'map, K: Index, V> IntoIterator for &'map mut IndexMap<K, V> {
    type Item = (K, &'map V);
    type IntoIter = IndexIterMut<'map, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K: Index + fmt::Debug, V: fmt::Debug> fmt::Debug for IndexMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self).finish()
    }
}
