#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::cfg(scrape_quals = true)] // TODO: needed due to odd cyclic constraint?

use std::vec::IntoIter;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(it: IntoIter<i32{v: 5 <= v}>))]
pub fn goo<I>(it: IntoIter<i32>) {
    for x in it {
        assert(0 <= x);
        assert(1 <= x);
        assert(5 <= x); // would fail without scrape
        assert(6 <= x); //~ ERROR refinement type
    }
}
