#![flux::defs {
    fn map_set(m:Map<int, int>, k: int, v: int) -> Map<int, int> { map_store(m, k, v) }
    fn map_get(m: Map<int,int>, k:int) -> int { map_select(m, k) }
    fn map_def(v:int) -> Map<int, int> { map_default(v) }
    fn set_add(x: int, s: Set<int>) -> Set<int> { set_union(set_singleton(x), s) }
    fn set_is_empty(s: Set<int>) -> bool { s == set_empty(0) }
    fn set_emp() -> Set<int> { set_empty(0) }
}]

/// define a type indexed by a map
#[flux::opaque]
#[flux::refined_by(keys: Set<int>, vals: Map<int, int>)]
pub struct RMap {
    inner: std::collections::HashMap<i32, i32>,
}

impl RMap {
    #[flux::trusted]
    #[flux::sig(fn() -> RMap[set_empty(0), map_def(0)])]
    pub fn new() -> Self {
        Self { inner: std::collections::HashMap::new() }
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &strg RMap[@m], k: i32, v: i32)
                ensures self: RMap[set_add(k, m.keys), map_set(m.vals, k, v)])]
    pub fn set(&mut self, k: i32, v: i32) {
        self.inner.insert(k, v);
    }

    #[flux::trusted]
    #[flux::sig(fn(&RMap[@m], k: i32 where set_mem(k,m.keys)) -> i32[map_get(m.vals, k)])]
    pub fn get(&self, k: i32) -> Option<i32> {
        self.inner.get(&k).copied()
    }
}
