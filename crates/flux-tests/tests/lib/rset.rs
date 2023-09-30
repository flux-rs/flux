#![allow(dead_code)]
#![flux::defs {
    fn set_add(x: int, s: Set<int>) -> Set<int> { set_union(set_singleton(x), s) }
    fn set_is_empty(s: Set<int>) -> bool { s == set_empty(0) }
    fn set_emp() -> Set<int> { set_empty(0) }
}]

#[flux::opaque]
#[flux::refined_by(elems: Set<T>)]
pub struct RSet<T> {
    inner: std::collections::HashSet<T>,
}

impl RSet<T> {
    #[flux::trusted]
    #[flux::sig(fn() -> RSet[set_empty(0)])]
    pub fn new() -> Self {
        Self { inner: std::collections::HashSet::new() }
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &strg RSet[@s], elem: T)
                ensures self: RSet[set_add(k, s.elems)])]
    pub fn insert(&mut self, elem: T) {
        self.inner.insert(elem);
    }

    #[flux::trusted]
    #[flux::sig(fn(&Set[@s], &T[@elem]) -> bool[set_is_in(elem, s.elems)])]
    pub fn contains(&self, elem: &T) -> bool {
        self.inner.contains(elem)
    }
}

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

fn test() {
    let mut s = RSet::new();
    s.insert(1);
    assert(s.contains(1));
    assert(!s.contains(2));
}
