//@ignore-test: ignored as its crashing in normalization :-(
#![allow(unused)]
#![feature(allocator_api)]

use std::{
    alloc::{Allocator, Global},
    ops::{Index, IndexMut},
    slice::{Iter, SliceIndex},
};

use flux_rs::extern_spec;

// needed for the iter-spec which indexes options
#[path = "../../lib/option.rs"]
mod option;

#[path = "../../lib/slice.rs"]
mod slice;

#[path = "../../lib/vec.rs"]
mod vec;

#[path = "../../lib/iter.rs"]
mod iter;

// -------------------------------------------------------------------------------------

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(slice: &[u8][@n]) -> Vec<u8>[n])]
fn test_map_slice(slice: &[u8]) -> Vec<u8> {
    slice.iter().map(|n| n + 2).collect()
}

// #[flux::sig(fn(slice: &[u8][@n]) -> Vec<u8>[n])]
// fn test_iter_collect(slice: &[u8]) -> Vec<u8> {
//     slice.into_iter().collect()
// }
