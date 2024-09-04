#![feature(allocator_api)]

use std::alloc::{Allocator, Global};

use flux_rs::extern_spec;

#[extern_spec]
#[refined_by(len: int)]
struct Vec<T, A: Allocator = Global>;

#[extern_spec]
impl<T> Vec<T> {
    #[sig(fn() -> Vec<T>[0])]
    fn new() -> Vec<T>;
}

#[extern_spec]
impl<T, A: Allocator> Vec<T, A> {
    #[sig(fn(self: &strg Vec<T, A>[@n], T) ensures self: Vec<T, A>[n+1])]
    fn push(&mut self, value: T);

    #[sig(fn(&Vec<T, A>[@n]) -> usize[n])]
    fn len(&self) -> usize;

    #[sig(fn(&Vec<T, A>[@n]) -> bool[n == 0])]
    fn is_empty(&self) -> bool;
}

#[extern_spec]
impl<T> [T] {
    #[sig(fn(self: Box<[T][@n], A>) -> Vec<T, A>[n])]
    fn into_vec<A>(self: Box<[T], A>) -> Vec<T, A>
    where
        A: Allocator;
}

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

#[flux::sig(fn() -> Vec<i32>[3])]
pub fn test_vec_macro() -> Vec<i32> {
    vec![10, 20, 30]
}

#[flux::sig(fn() -> Vec<i32>[3])]
pub fn test_push() -> Vec<i32> {
    let mut res = Vec::new();
    res.push(10);
    res.push(20);
    res.push(30);
    res
}

#[flux::sig(fn() -> usize[3])]
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
