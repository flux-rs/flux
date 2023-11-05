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

use flux_rs::extern_spec;
#[flux::extern_spec]
#[allow(unused, dead_code)]
#[flux::refined_by(elems : Set < T >)]
struct __FluxExternStructHashSet<T, S = RandomState>(HashSet<T, S>);
struct __FluxExternImplStructHashSet<Tiger: Eq + Hash>(HashSet<Tiger>);
#[flux::generics(Tiger as base)]
impl<Tiger: Eq + Hash> __FluxExternImplStructHashSet<Tiger> {
    #[flux::extern_spec]
    #[flux::sig(fn() -> HashSet < Tiger > [set_empty(0)])]
    fn new() -> HashSet<Tiger> {
        <HashSet<Tiger>>::new()
    }

    #[flux::sig(fn(set: &strg HashSet<Tiger>[@s], elem:Tiger) -> bool ensures set: HashSet<Tiger>[set_union(set_singleton(elem), s)])]
    fn insert(s: &mut HashSet<Tiger>, elem: Tiger) -> bool {
        s.insert(elem)
    }

    #[flux::sig(fn(set: &HashSet<Tiger>[@s], &Tiger[@elem]) -> bool[set_is_in(elem, s.elems)])]
    fn contains(set: &HashSet<Tiger>, elem: &Tiger) -> bool {
        set.contains(elem)
    }
}
#[flux::sig(fn(bool [true]))]
fn assert(_b: bool) {}
pub fn test() {
    let mut s: HashSet<i32> = HashSet::new();
    let v0 = 666;
    let v1 = 667;
    s.insert(v0);
    // for v in &s {
    //     assert(*v >= 666);
    // }
    assert(s.contains(&v0));
    assert(!s.contains(&v1));
}
