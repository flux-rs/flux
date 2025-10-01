#![allow(dead_code)]

use std::hash::Hash;

#[flux::opaque]
#[flux::refined_by(elems: Set<T>)]
pub struct RSet<T> {
    pub inner: std::collections::HashSet<T>,
}

// TODO: (RJ) I get some odd error with `T as spl` / cannot refine if I just remove this annotation!
// error: internal compiler error: crates/flux-middle/src/rty/subst.rs:353:30: expected base type for generic parameter, found `∃int. { i32[^0#0] | * }`
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

    #[flux::trusted]
    pub fn iter(self: &Self) -> std::collections::hash_set::Iter<'_, T> {
        self.inner.iter()
    }

    #[flux::trusted]
    #[flux::sig(fn(&RSet<T>[@self], &RSet<T>[@other]) -> RSet<T>[set_intersection(self, other)])]
    pub fn intersection(&self, other: &RSet<T>) -> RSet<T>
    where
        T: Eq + Hash + Clone,
    {
        let inner = self.inner.intersection(&other.inner).cloned().collect();
        RSet { inner }
    }

    #[flux::trusted]
    #[flux::sig(fn(&RSet<T>[@self], &RSet<T>[@other]) -> RSet<T>[set_union(self, other)])]
    pub fn union(&self, other: &RSet<T>) -> RSet<T>
    where
        T: Eq + Hash + Clone,
    {
        let inner = self.inner.union(&other.inner).cloned().collect();
        RSet { inner }
    }
}
