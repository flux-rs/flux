#![allow(unused)]
use std::{iter::Enumerate, slice::Iter};

extern crate flux_core;

#[path = "../../lib/iter.rs"]
mod iter;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(slice: &[u8]{n: n > 0}))]
fn test_iter1_neg(slice: &[u8]) {
    assert(slice.len() > 0);
    let mut iter = slice.iter();
    let next = iter.next();
    assert(next.is_some());
    assert(iter.next().is_some()); //~ ERROR refinement type
}
