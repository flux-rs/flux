use std::collections::HashMap;

pub struct ScopedHashMap<K, V>(Vec<HashMap<K, V>>);

impl<K, V> ScopedHashMap<K, V> {
    pub fn new() -> Self {
        Self(vec![HashMap::new()])
    }

    pub fn enter_scope<T>(&mut self, f: impl for<'a> FnOnce(&'a mut Self) -> T) -> T {
        self.0.push(HashMap::new());
        let t = f(self);
        self.0.pop();
        t
    }
}

impl<K, V> ScopedHashMap<K, V>
where
    K: Eq + std::hash::Hash,
{
    pub fn insert(&mut self, k: K, v: V) {
        self.0.last_mut().unwrap().insert(k, v);
    }
}

impl<'a, K, Q: ?Sized, V> std::ops::Index<&'a Q> for ScopedHashMap<K, V>
where
    K: Eq + std::hash::Hash + std::borrow::Borrow<Q>,
    Q: Eq + std::hash::Hash,
{
    type Output = V;

    fn index(&self, index: &'a Q) -> &Self::Output {
        for frame in self.0.iter().rev() {
            if let Some(v) = frame.get(index) {
                return v;
            }
        }
        panic!("no entry found for key");
    }
}

#[derive(Clone)]
pub struct OrderedHashMap<K, V> {
    map: HashMap<K, V>,
    keys: Vec<K>,
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
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
        self.keys.iter().map(move |k| (k, &self.map[k]))
    }

    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq,
    {
        self.map.get(k)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V>
    where
        K: Copy,
    {
        self.keys.push(k);
        self.map.insert(k, v)
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
