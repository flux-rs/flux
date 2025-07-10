// see issue 1097 -- testing the specs for `map` and `for_each`

#![feature(step_trait, allocator_api)]
#![allow(unused)]

use flux_rs::attrs::*;
extern crate flux_core;

#[path = "../../lib/vec.rs"]
mod vec;

#[spec(fn (bool[true]))]
pub fn assert(b: bool) {}

#[spec(fn (vec1: &Vec<i32>[@n], vec2: &Vec<i32>[n]) -> i32)]
fn dot2(vec1: &Vec<i32>, vec2: &Vec<i32>) -> i32 {
    let n = vec1.len();
    let mut res = 0;
    (0..n).for_each(|i| res += vec1[i] * vec2[i]);
    res
}

fn test_map_err() -> Vec<i32> {
    #[spec(fn (i32{v: 100 <= v}) -> i32{v: 0 < v})]
    fn bar(x: i32) -> i32 {
        x + 1
    }
    (0..10).map(|i| bar(i)).collect() //~ ERROR refinement type
}

fn test_foreach_err() {
    (0..100).for_each(|i| {
        assert(0 <= i);
        assert(i < 10) //~ ERROR refinement type
    })
}
