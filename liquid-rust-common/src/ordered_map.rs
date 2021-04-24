use std::iter::FromIterator;

/// An associative array that preserves insertion order.
#[derive(Default)]
pub struct OrderedMap<K, V> {
    inner: Vec<(K, V)>,
}

impl<K, V> OrderedMap<K, V> {
    pub fn new() -> Self {
        OrderedMap { inner: Vec::new() }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.inner.iter().map(|(k, v)| (k, v))
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

impl<K, V> OrderedMap<K, V>
where
    K: Eq,
{
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        for (curr_k, curr_v) in self.inner.iter_mut() {
            if k == *curr_k {
                return Some(std::mem::replace(curr_v, v));
            }
        }

        self.inner.push((k, v));
        None
    }
}

impl<K, V> FromIterator<(K, V)> for OrderedMap<K, V>
where
    K: Eq,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self {
            inner: FromIterator::from_iter(iter),
        }
    }
}

impl<Q, K, V> std::ops::Index<&'_ Q> for OrderedMap<K, V>
where
    K: Eq + std::borrow::Borrow<Q>,
    Q: Eq,
{
    type Output = V;

    fn index(&self, index: &'_ Q) -> &Self::Output {
        for (k, v) in self.iter() {
            if k.borrow() == index {
                return v;
            }
        }

        panic!("Key not found");
    }
}

impl<'a, K, V> IntoIterator for &'a OrderedMap<K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
