#![allow(dead_code)]
#![flux::defs {
    fn map_set<K, V>(m:Map<K, V>, k: K, v: V) -> Map<K, V> { map_store(m, k, v) }
    fn map_get<K, V>(m: Map<K, V>, k:K) -> V { map_select(m, k) }
    fn map_def<K, V>(v:V) -> Map<K, V> { map_default(v) }
    fn set_add<T>(x: T, s: Set<T>) -> Set<T> { set_union(set_singleton(x), s) }
    fn set_is_empty<T>(s: Set<T>) -> bool { s == set_empty(0) }
    fn set_emp<T>() -> Set<T> { set_empty(0) }
}]

use std::hash::Hash;

/// define a type indexed by a map
#[flux::opaque]
#[flux::refined_by(keys: Set<K>, vals: Map<K, V>)]
pub struct RMap<K, V> {
    inner: std::collections::HashMap<K, V>,
}

#[flux::generics(<K as base, V as base>)]
impl<K, V> RMap<K, V> {
    #[flux::trusted]
    #[flux::sig(fn() -> RMap<K, V>{m: m.keys == set_empty(0)})]
    pub fn new() -> Self {
        Self { inner: std::collections::HashMap::new() }
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &strg RMap<K, V>[@m], k: K, v: V)
                ensures self: RMap<K, V>[set_add(k, m.keys), map_set(m.vals, k, v)])]
    pub fn set(&mut self, k: K, v: V)
    where
        K: Eq + Hash,
    {
        self.inner.insert(k, v);
    }

    #[flux::trusted]
    #[flux::sig(fn(&RMap<K, V>[@m], &K[@k]) -> Option<&V[map_get(m.vals, k)]>)]
    pub fn get(&self, k: &K) -> Option<&V>
    where
        K: Eq + Hash,
    {
        self.inner.get(k)
    }

    #[flux::trusted]
    #[flux::sig(fn(&RMap<K,V>[@m], &K[@k]) -> &V[map_get(m.vals, k)] requires set_is_in(k, m.keys))]
    pub fn lookup(&self, k: &K) -> &V
    where
        K: Eq + Hash,
    {
        self.inner.get(k).unwrap()
    }

    #[flux::trusted]
    #[flux::sig(fn(&RMap<K,V>[@m], &K[@k]) -> bool[set_is_in(k, m.keys)])]
    pub fn contains(&self, k: &K) -> bool
    where
        K: Eq + Hash,
    {
        self.inner.contains_key(k)
    }
}
