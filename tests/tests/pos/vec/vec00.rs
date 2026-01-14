#![feature(allocator_api)]

extern crate flux_alloc;
extern crate flux_core;

use flux_rs::{assert, attrs::*};

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

#[spec(fn (x: &mut Vec<i32>[@n]) ensures x: Vec<i32>[#m])]
fn silly(x: &mut Vec<i32>) {}
