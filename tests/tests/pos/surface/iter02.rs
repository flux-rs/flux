#![allow(unused)]
#![feature(allocator_api)]

use std::{iter::Enumerate, slice::Iter};

extern crate flux_alloc;
extern crate flux_core;

#[path = "../../lib/vec.rs"]
mod vec;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

// Tests
#[flux::sig(fn(slice: &[u8]{n: n > 0}))]
fn test_iter1(slice: &[u8]) {
    let mut iter = slice.iter();
    let next = iter.next();
    assert(next.is_some());
}

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

#[flux::sig(fn(&[usize][@n]) )]
pub fn test_enumer4(slice: &[usize]) {
    for (idx, _) in slice.iter().enumerate() {
        assert(idx < slice.len())
    }
}
