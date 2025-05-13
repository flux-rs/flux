// see issue 1097

#![feature(step_trait, allocator_api)]
#![allow(unused)]

#[path = "../../lib/vec.rs"]
mod vec;

#[path = "../../lib/iterator.rs"]
mod iterator;

#[flux_rs::sig(fn (bool[true]))]
pub fn assert(b: bool) {}

// TODO: get `for_each` working for `Range`
#[flux_rs::sig(fn (vec1: &Vec<i32>[@n], vec2: &Vec<i32>[n]) -> i32)]
fn dot2(vec1: &Vec<i32>, vec2: &Vec<i32>) -> i32 {
    let n = vec1.len();
    let mut res = 0;
    (0..n).for_each(|i| res += vec1[i] * vec2[i]);
    res
}

#[flux::sig(fn (i32{v: 0 <= v}) -> i32{v: 0 < v})]
pub fn foo(x: i32) -> i32 {
    x + 1
}

// TODO: get `map` working for `Range`
fn test() -> Vec<i32> {
    (0..10).map(|i| foo(i)).collect()
}
