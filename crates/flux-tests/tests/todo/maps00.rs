// #![feature(register_tool)]
// #![register_tool(flux)]

#![feature(custom_inner_attributes)]
#![flux::defs {
    fn map_set(m:Map<int, int>, k: int, v: int) -> Map<int, int> { map_store(m, k, v) }
    fn map_get(m: Map<int,int>, k:int) -> int { map_select(m, k) }
    fn map_def(v:int) -> Map<int, int> { map_default(v) }
}]

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    assert(true);
    assert(1 == 2);
    assert(1 + 1 == 2)
}

/// define a type indexed by a map
#[flux::opaque]
#[flux::refined_by(map: Map<int, int>)]
struct MyMap {
    inner: std::collections::HashMap<i32, i32>,
}

impl MyMap {
    #[flux::trusted]
    pub fn new() -> Self {
        Self { inner: std::collections::HashMap::new() }
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &strg MyMap[@m], k: i32, v: i32) ensures self: MyMap[map_set(m, k, v)])]
    pub fn set(&mut self, k: i32, v: i32) {
        self.inner.insert(k, v);
    }

    #[flux::trusted]
    #[flux::sig(fn(&MyMap[@m], k: i32) -> Option<i32[map_get(m, k)]>)]
    pub fn get(&self, k: i32) -> Option<i32> {
        *self.inner.get(&k)
    }
}

/// USE the type
pub fn test() {
    let mut m = MyMap::new();
    m.set(10, 1);
    m.set(20, 2);

    assert(m.get(10).unwrap() == 1);
    assert(m.get(20).unwrap() == 2);
    assert(m.get(30).unwrap() == 3); //~ ERROR refinement type
}
