#![allow(unused)]
#![feature(allocator_api)]

use std::{
    alloc::{Allocator, Global},
    iter::Enumerate,
    ops::{Index, IndexMut},
    slice::{Iter, SliceIndex},
};

use flux_rs::extern_spec;

extern crate flux_core;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(n: usize, slice: &[u8][n]) -> usize[n])]
fn test_iter2(n: usize, slice: &[u8]) -> usize {
    let n = slice.len();
    let mut iter = slice.iter();
    let mut count = 0;
    while let Some(v) = iter.next() {
        count += 1;
    }
    assert(count < n); //~ ERROR refinement type
    count
}

#[flux::sig(fn(slice: &[u8][@n]) -> usize[n])]
fn test_iter_for_loop_slice(slice: &[u8]) -> usize {
    let n = slice.len();
    let mut count = 0;
    for v in slice {
        count += 1;
    }
    assert(count > n); //~ ERROR refinement type
    count
}
