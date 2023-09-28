#![allow(dead_code)]
#![flux::defs {
    fn map_set(m:Map<int, int>, k: int, v: int) -> Map<int, int> { map_store(m, k, v) }
    fn map_get(m: Map<int,int>, k:int) -> int { map_select(m, k) }
    fn map_def(v:int) -> Map<int, int> { map_default(v) }
}]

/// define a type indexed by a map
#[flux::opaque]
#[flux::refined_by(map: Map<int, int>)]
pub struct RMap {
    inner: std::collections::HashMap<i32, i32>,
}

impl RMap {
    #[flux::trusted]
    pub fn new() -> Self {
        Self { inner: std::collections::HashMap::new() }
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &strg RMap[@m], k: i32, v: i32) ensures self: RMap[map_set(m, k, v)])]
    pub fn set(&mut self, k: i32, v: i32) {
        self.inner.insert(k, v);
    }

    #[flux::trusted]
    #[flux::sig(fn(&RMap[@m], k: i32) -> Option<i32[map_get(m, k)]>)]
    pub fn get(&self, k: i32) -> Option<i32> {
        self.inner.get(&k).copied()
    }
}
