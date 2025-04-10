//@ignore-test: this test use to work because the extern spec for `contains` didn't use the extra `Q`
//parameter. To fix it we need to refine `Borrow` to state that it preserves the index and in particular
//that the sort of the borrowed item is the same.

#![flux::cfg(scrape_quals = true)]

use std::{
    borrow::Borrow,
    collections::{HashSet, hash_map::RandomState},
    hash::{BuildHasher, Hash},
};

use flux_rs::extern_spec;

// REFINE THE STRUCT

#[extern_spec]
#[flux::refined_by(elems: Set<T>)]
struct HashSet<T, S = RandomState>;

// FIRST IMPL

#[extern_spec]
impl<T: Eq + Hash> HashSet<T, RandomState> {
    #[flux::sig(fn() -> HashSet<T>[set_empty(0)])]
    fn new() -> HashSet<T>;
}

// SECOND IMPL

#[extern_spec]
impl<T: Eq + Hash, S: BuildHasher> HashSet<T, S> {
    #[flux::sig(fn(set: &strg HashSet<T, S>[@s], elem:T) -> bool ensures set: HashSet<T, S>[set_union(set_singleton(elem), s)])]
    fn insert(s: &mut HashSet<T, S>, elem: T) -> bool;

    #[flux::sig(fn(set: &HashSet<T, S>[@s], &Q[@elem]) -> bool[set_is_in(elem, s.elems)])]
    fn contains<Q>(set: &HashSet<T, S>, elem: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq;
}

#[flux::trusted]
#[flux::sig(fn(&HashSet<T>[@s], &T[@elem]) -> bool[set_is_in(elem, s.elems)])]
fn member<T: Eq + Hash>(s: &HashSet<T>, elem: &T) -> bool {
    s.contains(elem)
}

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let mut s = HashSet::new();
    let v0 = 666;

    let v1 = 667;
    s.insert(v0);
    assert(member(&s, &v0));
    assert(member(&s, &v1)); //~ ERROR refinement type
}
