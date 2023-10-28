#![allow(dead_code)]

use std::hash::Hash;

#[flux::opaque]
#[flux::refined_by(elems: Set<T>)]
pub struct RSet<T> {
    pub inner: std::collections::HashSet<T>,
}

#[flux::generics(T as base)]
impl<T> RSet<T> {
    #[flux::trusted]
    #[flux::sig(fn() -> RSet<T>[set_empty(0)])]
    pub fn new() -> RSet<T> {
        let inner = std::collections::HashSet::new();
        RSet { inner }
    }

    #[flux::trusted]
    #[flux::sig(fn (set: &strg RSet<T>[@s], elem: T) ensures set: RSet<T>[set_union(set_singleton(elem), s)])]
    pub fn insert(self: &mut Self, elem: T)
    where
        T: Eq + Hash,
    {
        self.inner.insert(elem);
    }

    #[flux::trusted]
    #[flux::sig(fn(set: &RSet<T>[@s], &T[@elem]) -> bool[set_is_in(elem, s.elems)])]
    pub fn contains(self: &Self, elem: &T) -> bool
    where
        T: Eq + Hash,
    {
        self.inner.contains(elem)
    }
}
