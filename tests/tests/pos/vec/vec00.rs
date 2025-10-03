#![feature(allocator_api)]

// extern crate flux_alloc;
extern crate flux_core;

use std::alloc::{Allocator, Global};

use flux_rs::{assert, attrs::*, extern_spec};

#[extern_spec]
#[refined_by(len: int)]
#[invariant(len >= 0)]
struct Vec<T, A: Allocator = Global>;

#[extern_spec]
impl<T> Vec<T> {
    #[spec(fn() -> Vec<T>[0])]
    fn new() -> Vec<T>;
}

#[extern_spec]
impl<T, A: Allocator> Vec<T, A> {
    #[spec(fn(self: &mut Vec<T, A>[@n], T) ensures self: Vec<T, A>[n+1])]
    fn push(&mut self, value: T);

    #[spec(fn(self: &Vec<T, A>[@n]) -> usize[n])]
    fn len(&self) -> usize;

    #[spec(fn(self: &Vec<T, A>[@n]) -> bool[n == 0])]
    fn is_empty(&self) -> bool;

    #[spec(fn(self: &mut Vec<T, A>[@n]) -> Option<T>[n > 0]
           ensures self: Vec<T, A>[if n > 0 { n - 1 } else { 0 }])]
    fn pop(&mut self) -> Option<T>;
}

#[extern_spec]
impl<T> [T] {
    #[spec(fn(self: Box<[T][@n], A>) -> Vec<T, A>[n])]
    fn into_vec<A>(self: Box<[T], A>) -> Vec<T, A>
    where
        A: Allocator;
}

#[spec(fn() -> Vec<i32>[3])]
pub fn test_vec_macro() -> Vec<i32> {
    vec![10, 20, 30]
}

#[spec(fn() -> Vec<i32>[4])]
pub fn test_push_macro() -> Vec<i32> {
    let res = vec![10, 20, 30, 40];
    assert(res.len() == 4);
    res
}

#[spec(fn() -> Vec<i32>[2])]
pub fn test_push() -> Vec<i32> {
    let mut res = Vec::new();
    res.push(10);
    res.push(20);
    res.push(30);
    let val = res.pop().unwrap();
    assert(val >= 10);
    res
}

#[spec(fn() -> usize[2])]
pub fn test_len() -> usize {
    let res = test_push();
    res.len()
}

pub fn test_is_empty() {
    let res = test_push();
    assert(!res.is_empty())
}

// TODO: https://github.com/flux-rs/flux/issues/578
// #[spec(fn (Vec<i32{v:10 <= v}>))]
// pub fn test3(xs: Vec<i32>) {
//     for x in &xs {
//         assert(0 <= *x)
//     }
// }

#[spec(fn (vec: &mut Vec<T>[@n]) -> Option<(T, T)>
       requires n > 2
       ensures vec: Vec<T>[n-2])]
pub fn pop2<T>(vec: &mut Vec<T>) -> Option<(T, T)> {
    let v1 = vec.pop().unwrap();
    let v2 = vec.pop().unwrap();
    Some((v1, v2))
}
