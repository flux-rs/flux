use std::collections::HashMap;

pub trait Dict<K> {
    type Output;
    fn get<Q: ?Sized>(&self, k: &Q) -> Option<&Self::Output>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq;

    fn insert(&mut self, k: K, v: Self::Output);
}

impl<K: Eq + std::hash::Hash, V> Dict<K> for HashMap<K, V> {
    type Output = V;
    fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq,
    {
        HashMap::get(self, k)
    }

    fn insert(&mut self, k: K, v: V) {
        self.insert(k, v);
    }
}

#[derive(Debug, Default)]
pub struct Scoped<T>(Vec<T>);

impl<K, V, T> Dict<K> for Scoped<T>
where
    T: Dict<K, Output = V>,
{
    type Output = V;

    fn insert(&mut self, k: K, v: V) {
        self.0.last_mut().unwrap().insert(k, v);
    }

    fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq,
    {
        for frame in self.0.iter().rev() {
            if let Some(v) = frame.get(k) {
                return Some(v);
            }
        }
        None
    }
}

impl<T> Scoped<T> {
    pub fn push(&mut self, frame: T) {
        self.0.push(frame);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.0.pop()
    }
}

impl<K: Eq + std::hash::Hash, V: Sized> Scoped<OrderedHashMap<K, V>> {
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> + '_ {
        self.0.iter().flat_map(|x| x.iter())
    }
}

impl<K, V, T> std::ops::Index<K> for Scoped<T>
where
    T: Dict<K, Output = V>,
    K: Eq + std::hash::Hash,
{
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        self.get(&index).expect("no entry found for key")
    }
}

#[derive(Debug, Clone)]
pub struct OrderedHashMap<K, V> {
    map: HashMap<K, V>,
    keys: Vec<K>,
}

impl<K, V> Default for OrderedHashMap<K, V> {
    fn default() -> Self {
        Self {
            map: HashMap::default(),
            keys: Vec::default(),
        }
    }
}

impl<K, V> OrderedHashMap<K, V>
where
    K: Copy,
{
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            keys: Vec::new(),
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = K> + '_ {
        self.keys.iter().copied()
    }
}

impl<K, V> OrderedHashMap<K, V>
where
    K: Eq + std::hash::Hash,
{
    pub fn iter(&self) -> OrderedHashMapIter<'_, K, V> {
        OrderedHashMapIter {
            keys_iter: self.keys.iter(),
            map: self,
        }
    }
}

impl<K: Eq + std::hash::Hash + Copy, V> Dict<K> for OrderedHashMap<K, V> {
    type Output = V;

    fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq,
    {
        self.map.get(k)
    }

    fn insert(&mut self, k: K, v: V) {
        if self.map.insert(k, v).is_none() {
            self.keys.push(k);
        };
    }
}

impl<'a, K, Q: ?Sized, V> std::ops::Index<&'a Q> for OrderedHashMap<K, V>
where
    K: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash,
{
    type Output = V;

    fn index(&self, index: &'a Q) -> &Self::Output {
        &self.map[index]
    }
}

impl<K, V> std::iter::FromIterator<(K, V)> for OrderedHashMap<K, V>
where
    K: Eq + std::hash::Hash + Copy,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut keys = Vec::new();
        let map = iter.into_iter().inspect(|(k, _)| keys.push(*k)).collect();
        Self { keys, map }
    }
}

pub struct OrderedHashMapIter<'a, K, V> {
    keys_iter: std::slice::Iter<'a, K>,
    map: &'a OrderedHashMap<K, V>,
}

impl<'a, K: Eq + std::hash::Hash, V> Iterator for OrderedHashMapIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(k) = self.keys_iter.next() {
            Some((k, &self.map[k]))
        } else {
            None
        }
    }
}
impl<'a, K: Eq + std::hash::Hash, V> DoubleEndedIterator for OrderedHashMapIter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(k) = self.keys_iter.next_back() {
            Some((k, &self.map[k]))
        } else {
            None
        }
    }
}

impl<'a, K: Eq + std::hash::Hash, V> IntoIterator for &'a OrderedHashMap<K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = OrderedHashMapIter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct OrderedHashMapIntoIter<K, V> {
    keys_iter: std::vec::IntoIter<K>,
    map: HashMap<K, V>,
}

impl<K: Eq + std::hash::Hash, V> Iterator for OrderedHashMapIntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(k) = self.keys_iter.next() {
            let v = self.map.remove(&k).unwrap();
            Some((k, v))
        } else {
            None
        }
    }
}

impl<K: Eq + std::hash::Hash, V> DoubleEndedIterator for OrderedHashMapIntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(k) = self.keys_iter.next_back() {
            let v = self.map.remove(&k).unwrap();
            Some((k, v))
        } else {
            None
        }
    }
}

impl<K: Eq + std::hash::Hash, V> IntoIterator for OrderedHashMap<K, V> {
    type Item = (K, V);

    type IntoIter = OrderedHashMapIntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        OrderedHashMapIntoIter {
            keys_iter: self.keys.into_iter(),
            map: self.map,
        }
    }
}
