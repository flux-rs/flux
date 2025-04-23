#![allow(unused)]
#![feature(allocator_api)]

use std::{iter::Enumerate, slice::Iter};

#[path = "../../lib/option.rs"]
mod option;

#[path = "../../lib/slice.rs"]
mod slice;

#[path = "../../lib/vec.rs"]
mod vec;

#[path = "../../lib/iter.rs"]
mod iter;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

// Tests
#[flux::sig(fn(slice: &[u8]{n: n > 0}))]
fn test_iter1(slice: &[u8]) {
    let mut iter = slice.iter();
    let next = iter.next();
    assert(next.is_some());
}

#[flux::sig(fn(n: usize, slice: &[u8][n]) -> usize[n])]
fn test_iter2(n: usize, slice: &[u8]) -> usize {
    let n = slice.len();
    let mut iter = slice.iter();
    let mut count = 0;
    while let Some(v) = iter.next() {
        count += 1;
    }
    assert(count == n);
    count
}

#[flux::sig(fn(slice: &[u8][@n]) -> usize[n])]
fn test_iter_for_loop_slice(slice: &[u8]) -> usize {
    let n = slice.len();
    let mut count = 0;
    for v in slice {
        count += 1;
    }
    assert(count == n);
    count
}

// #[flux::sig(fn(slice: &Vec<u8>[@n]) -> usize[n])]
// fn test_iter_for_loop_vec(vec: &Vec<u8>) -> usize {
//     let n = vec.len();
//     let mut count = 0;
//     for v in vec {
//         count += 1;
//     }
//     // assert(count == n);
//     count
// }

#[flux::sig(fn(slice: &[u8]{n: n > 1}))]
fn test_enumerate1(slice: &[u8]) {
    assert(slice.len() > 0);
    let mut enumer = slice.iter().enumerate();

    let next = enumer.next();
    assert(next.is_some());
    let (idx, _) = next.unwrap();
    assert(idx == 0);

    let next_next = enumer.next();
    assert(next_next.is_some());
    let (idx, _) = next_next.unwrap();
    assert(idx == 1);
}

#[flux::sig(fn(&[usize][1]) )]
pub fn test_enumer2(slice: &[usize]) {
    assert(slice.len() == 1);
    let mut enumer = slice.iter().enumerate();

    let next = enumer.next();
    assert(next.is_some());

    let next_next = enumer.next();
    assert(next_next.is_none())
}

#[flux::sig(fn(&[usize][@n]) )]
pub fn test_enumer3(slice: &[usize]) {
    let mut e = slice.iter().enumerate();
    while let Some((idx, _)) = e.next() {
        assert(idx < slice.len())
    }
}
