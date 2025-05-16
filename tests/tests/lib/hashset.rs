use std::{collections::HashSet, hash::RandomState};

use flux_rs::attrs::*;

#[extern_spec]
#[refined_by(elems: Set<T>)]
struct HashSet<T, S = RandomState>;

#[extern_spec]
impl<T, S> HashSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    #[sig(fn() -> HashSet<T, S>[set_empty(0)])]
    fn new() -> HashSet<T, S>;

    #[sig(fn(&mut HashSet<T, S>[@s], T[@x]) -> bool[set_contains(s, x)])]
    pub fn insert(&mut self, value: T) -> bool;
}

// impl<T> RSet<T> {
//     #[flux::trusted]
//     #[flux::sig(fn() -> RSet<T>[set_empty(0)])]
//     pub fn new() -> RSet<T> {
//         let inner = std::collections::HashSet::new();
//         RSet { inner }
//     }

//     #[flux::trusted]
//     #[flux::sig(fn (set: &strg RSet<T>[@s], elem: T) ensures set: RSet<T>[set_union(set_singleton(elem), s)])]
//     pub fn insert(self: &mut Self, elem: T)
//     where
//         T: Eq + Hash,
//     {
//         self.inner.insert(elem);
//     }

//     #[flux::trusted]
//     #[flux::sig(fn(set: &RSet<T>[@s], &T[@elem]) -> bool[set_is_in(elem, s.elems)])]
//     pub fn contains(self: &Self, elem: &T) -> bool
//     where
//         T: Eq + Hash,
//     {
//         self.inner.contains(elem)
//     }

//     #[flux::trusted]
//     pub fn iter(self: &Self) -> std::collections::hash_set::Iter<T> {
//         self.inner.iter()
//     }
// }
