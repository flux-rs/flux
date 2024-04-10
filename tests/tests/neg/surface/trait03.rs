#![flux::cfg(scrape_quals = true)] // TODO: needed due to odd cyclic constraint?

use std::vec::IntoIter;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

// These assertions expect for the last one, should verify once we implement trait bounds properly
#[flux::sig(fn(it: IntoIter<i32{v: 5 <= v}>))]
pub fn goo<I>(it: IntoIter<i32>) {
    for x in it {
        assert(0 <= x); //~ERROR refinement type error
        assert(1 <= x); //~ERROR refinement type error
        assert(5 <= x); // would fail without scrape
                        //~^ ERROR refinement type error
        assert(6 <= x); //~ ERROR refinement type
    }
}
