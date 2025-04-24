#![feature(step_trait)]
#![allow(unused)]
#![feature(allocator_api)]

use std::ops::Index;

#[path = "../../lib/vec.rs"]
mod vec;

#[path = "../../lib/iterator.rs"]
mod iterator;

// #[flux_rs::sig(fn (bool[true]))]
// fn assert(b: bool) {}
//
// #[flux::sig(fn () -> Vec<i32>[2])]
// fn test0() -> Vec<i32> {
//     let mut v = Vec::new();
//     v.push(10);
//     v.push(20);
//     v
// }

#[flux::sig(fn (&Vec<i32>[@n]) -> Vec<i32>[n])]
fn test_push_iter(vec: &Vec<i32>) -> Vec<i32> {
    let mut res = Vec::new();
    for v in vec.iter() {
        res.push(*v + 10);
    }
    res
}

// #[flux::sig(fn (&Vec<i32>[@n]) -> Vec<i32>[n])]
// fn test2(vec: &Vec<i32>) -> Vec<i32> {
//     vec.iter().map(|x| *x + 10).collect()
// }
