#![feature(allocator_api)]
#![feature(associated_type_bounds)]

use std::alloc::{Allocator, Global};

use flux_rs::extern_spec;

#[extern_spec]
#[flux::refined_by(len: int)]
struct Vec<T, A: Allocator = Global>;

#[extern_spec]
impl<T> Vec<T> {
    #[flux::sig(fn() -> Vec<T>[0])]
    fn new() -> Vec<T>;
}

#[extern_spec]
impl<T, A: Allocator> Vec<T, A> {
    #[flux::sig(fn(self: &strg Vec<T, A>[@n], T) ensures self: Vec<T, A>[n+1])]
    fn push(v: &mut Vec<T, A>, value: T);

    #[flux::sig(fn(&Vec<T, A>[@n]) -> usize[n])]
    fn len(v: &Vec<T, A>) -> usize;

    #[flux::sig(fn(&Vec<T, A>[@n]) -> bool[n == 0])]
    fn is_empty(v: &Vec<T, A>) -> bool;
}

// TODO: unsupported statements in vec!
// FIX: write our own!
// pub fn test1() -> Vec<i32> {
//     let v = vec![1, 2];
//     v
// }

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

#[flux::sig(fn () -> Vec<i32>[3])]
pub fn test_push() -> Vec<i32> {
    let mut res = Vec::new();
    res.push(10);
    res.push(20);
    res.push(30);
    res
}

#[flux::sig(fn () -> usize[3])]
pub fn test_len() -> usize {
    let res = test_push();
    res.len()
}

pub fn test_is_empty() {
    let res = test_push();
    assert(!res.is_empty())
}

// TODO: https://github.com/flux-rs/flux/issues/578
// #[flux::sig(fn (Vec<i32{v:10 <= v}>))]
// pub fn test3(xs: Vec<i32>) {
//     for x in &xs {
//         assert(0 <= *x)
//     }
// }
