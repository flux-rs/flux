extern crate std;
use std::{
    collections::{hash_map::RandomState, HashSet},
    hash::Hash,
};

#[flux::extern_spec]
#[allow(unused, dead_code)]
#[flux::refined_by(elems : Set < T >)]
struct __FluxExternStructHashSet<T, S = RandomState>(HashSet<T, S>);
struct __FluxExternImplStructHashSet<T: Eq + Hash, S = RandomState>(HashSet<T, S>);
#[flux::generics(T as base, S)]
impl<T: Eq + Hash, S> __FluxExternImplStructHashSet<T, S> {
    #[allow(dead_code)]
    #[flux::extern_spec]
    #[flux::trusted]
    #[flux::sig(fn() -> HashSet < T > [set_empty(0)])]
    fn new() -> HashSet<T> {
        <HashSet<T>>::new()
    }
    #[allow(dead_code)]
    #[flux::extern_spec]
    #[flux::trusted]
    #[flux::sig(fn(set: &strg HashSet<T>[@s], elem:T) -> bool ensures set: HashSet<T>[set_union(set_singleton(elem), s)])]
    fn insert(s: &mut HashSet<T>, elem: T) -> bool {
        <HashSet<T>>::insert(s, elem)
    }
}

#[flux::trusted]
#[flux::sig(fn<T as base>(&HashSet<T>[@s], &T[@elem]) -> bool[set_is_in(elem, s.elems)])]
fn member<T: Eq + Hash>(s: &HashSet<T>, elem: &T) -> bool {
    s.contains(elem)
}

#[flux::sig(fn(bool [true]))]
fn assert(_b: bool) {}
pub fn test() {
    let mut s: HashSet<i32> = HashSet::new();
    let v0 = 666;
    let v1 = 667;
    s.insert(v0);
    assert(member(&s, &v0));
    assert(!member(&s, &v1));
}
