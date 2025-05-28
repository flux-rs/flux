#![allow(unused)]
#![feature(allocator_api)]

use std::{
    alloc::{Allocator, Global},
    iter::Enumerate,
    ops::{Index, IndexMut},
    slice::{Iter, SliceIndex},
};

use flux_rs::extern_spec;

// needed for the iter-spec which indexes options
#[path = "../../lib/option.rs"]
mod option;

#[path = "../../lib/vec.rs"]
mod vec;

#[path = "../../lib/iter.rs"]
mod iter;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(slice: &Vec<u8>[@n]) -> usize[n])]
fn test_iter_for_loop_vec(vec: &Vec<u8>) -> usize {
    let n = vec.len();
    let mut count = 0;
    for v in vec {
        count += 1;
    }
    count+1   //~ ERROR refinement type 
}

#[flux::sig(fn(slice: &Vec<u8>[@n]) -> Vec<u8>[10])]
fn test_iter_for_loop_vec2(vec: &Vec<u8>) -> Vec<u8> {
    let n = vec.len();
    let mut res = Vec::new();
    for v in vec {
        res.push(*v);
    }
    res //~ ERROR refinement type
}
