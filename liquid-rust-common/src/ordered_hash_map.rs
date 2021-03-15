use std::iter::FromIterator;

/// A hash map that preserves insertion order.
#[derive(Default)]
pub struct OrderedHashMap<K, V> {
    // IndexMap preserves insertion order as long as swap_remove and related methods are not used.
    inner: indexmap::IndexMap<K, V>,
}

impl<K, V> OrderedHashMap<K, V> {
    pub fn new() -> Self {
        OrderedHashMap {
            inner: indexmap::IndexMap::new(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.inner.iter()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn truncate(&mut self, n: usize) {
        self.inner.truncate(n)
    }
}

impl<K, V> FromIterator<(K, V)> for OrderedHashMap<K, V>
where
    K: Eq + std::hash::Hash,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self {
            inner: FromIterator::from_iter(iter),
        }
    }
}

impl<K, V> OrderedHashMap<K, V>
where
    K: Eq + std::hash::Hash,
{
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.inner.insert(k, v)
    }
}

impl<Q, K, V> std::ops::Index<&'_ Q> for OrderedHashMap<K, V>
where
    K: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash,
{
    type Output = V;

    fn index(&self, index: &'_ Q) -> &Self::Output {
        &self.inner[index]
    }
}
