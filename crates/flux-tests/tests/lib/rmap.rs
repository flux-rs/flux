#![allow(dead_code)]
#![flux::defs {
    fn map_set<K, V>(m:Map<K, V>, k: K, v: V) -> Map<K, V> { map_store(m, k, v) }
    fn map_get<K, V>(m: Map<K, V>, k:K) -> V { map_select(m, k) }
    fn map_def<K, V>(v:V) -> Map<K, V> { map_default(v) }
}]

use std::hash::Hash;

/// define a type indexed by a map
#[flux::opaque]
#[flux::refined_by(<K, V> { vals: Map<K, V> } )]
pub struct RMap<K, V> {
    inner: std::collections::HashMap<K, V>,
}

#[flux::generics(K as base, V as base)]
impl<K, V> RMap<K, V> {
    #[flux::trusted]

    /// #[flux::sig(fn() -> RMap<K, V>{m: true})]   "OK"    i.e. wraps K, V in existential
    /// #[flux::sig(fn() -> RMap<K, V>{m: true})]   "CRASH" i.e. wraps K, V in LAMBDA
    pub fn new() -> Self {
        Self { inner: std::collections::HashMap::new() }
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &strg RMap<K,V>[@m], k: K, v: V) ensures self: RMap<K,V>[map_set(m.vals, k, v)])]
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
}
