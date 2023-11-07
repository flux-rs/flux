// #![feature(prelude_import)]
// #![flux::cfg(scrape_quals = true)]
// // #![feature(register_tool, custom_inner_attributes)]
// #![register_tool(flux)]
// #![register_tool(flux_tool)]
// #[prelude_import]
// use std::prelude::rust_2021::*;
// #[macro_use]
extern crate std;
use std::{
    collections::{hash_map::RandomState, HashSet},
    hash::Hash,
};

#[flux::extern_spec]
#[allow(unused, dead_code)]
#[flux::refined_by(elems : Set < T >)]
struct __FluxExternStructHashSet<T, S = RandomState>(HashSet<T, S>);
struct __FluxExternImplStructHashSet<Tiger: Eq + Hash, S = RandomState>(HashSet<Tiger, S>);
#[flux::generics(Tiger as base, S)]
impl<Tiger: Eq + Hash, S> __FluxExternImplStructHashSet<Tiger, S> {
    #[allow(dead_code)]
    #[flux::extern_spec]
    #[flux::trusted]
    #[flux::sig(fn() -> HashSet < Tiger > [set_empty(0)])]
    fn new() -> HashSet<Tiger> {
        <HashSet<Tiger>>::new()
    }

    #[allow(dead_code)]
    #[flux::extern_spec]
    #[flux::trusted]
    #[flux::sig(fn(set: &strg HashSet<Tiger>[@s], elem:Tiger) -> bool ensures set: HashSet<Tiger>[set_union(set_singleton(elem), s)])]
    fn insert(s: &mut HashSet<Tiger>, elem: Tiger) -> bool {
        <HashSet<Tiger>>::insert(s, elem)
    }

    // // NASTY PROBLEM: `contains` takes a `&Q` where the hash must be the same (yuck).
    // #[flux::extern_spec]
    // #[flux::trusted]
    // #[flux::sig(fn(set: &HashSet<Tiger>[@s], &Quux[@elem]) -> bool[set_is_in(elem, s.elems)])]
    // fn contains<Quux>(set: &HashSet<Tiger>, elem: &Quux) -> bool {
    //     <HashSet<Tiger>>::contains(set, elem)
    // }
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
