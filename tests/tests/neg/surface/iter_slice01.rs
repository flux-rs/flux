#![allow(unused)]
#![feature(allocator_api)]

use std::{
    alloc::{Allocator, Global},
    ops::{Index, IndexMut},
    slice::{Iter, SliceIndex},
};

use flux_rs::extern_spec;

extern crate flux_alloc;
extern crate flux_core;

// -------------------------------------------------------------------------------------

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(slice: &[u8][@n]) -> Vec<u8>[n-1])]
fn test_map_slice(slice: &[u8]) -> Vec<u8> {
    slice.iter().map(|n| n + 2).collect() //~ ERROR refinement type
}

#[flux::sig(fn(slice: &[u8][@n]) -> Vec<u8>[n-2] requires n >= 2 )]
fn test_skip_slice(slice: &[u8]) -> Vec<u8> {
    slice.iter().skip(1).map(|n| n + 2).collect() //~ ERROR refinement type
}
