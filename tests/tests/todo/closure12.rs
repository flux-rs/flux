// see issue 1097

#![feature(step_trait, allocator_api)]
#![allow(unused)]

use flux_rs::attrs::*;

#[path = "../lib/vec.rs"]
mod vec;

#[path = "../lib/iterator.rs"]
mod iterator;

#[spec(fn (bool[true]))]
pub fn assert(b: bool) {}

// TODO: get `for_each` working for `Range`
#[spec(fn (vec1: &Vec<i32>[@n], vec2: &Vec<i32>[n]) -> i32)]
fn dot2(vec1: &Vec<i32>, vec2: &Vec<i32>) -> i32 {
    let n = vec1.len();
    let mut res = 0;
    (0..n).for_each(|i| res += vec1[i] * vec2[i]);
    res
}

#[spec(fn (i32{v: 0 <= v}) -> i32{v: 0 < v})]
pub fn foo(x: i32) -> i32 {
    x + 1
}

fn test_map() -> Vec<i32> {
    (0..10).map(|i| foo(i)).collect()
}

fn test_foreach() {
    (0..100).for_each(|i| {
        assert(0 <= i);
        assert(i < 10)
    })
}

#[spec(fn(n: usize, f:F) -> Vec<A>[n])]
fn fill_vec<F, A>(n: usize, mut f: F) -> Vec<A>
where
    F: FnMut() -> A,
{
    // let mut res = RVec::new();
    // for _ in 0..n {
    //     res.push(f());
    // }
    // res
    (0..n).map(|_| f()).collect()
}

#[spec(fn(n: usize, f:F) -> Vec<A>[n] where F: FnMut(usize{v:0<=v && v <n}) -> A)]
fn fill_vec_index<F, A>(n: usize, mut f: F) -> Vec<A>
where
    F: FnMut(usize) -> A,
{
    // let mut res = RVec::new();
    // for _ in 0..n {
    //     res.push(f());
    // }
    // res
    (0..n).map(|i| f(i)).collect()
}

#[spec(fn(x: &Vec<i32>[@n], y: &Vec<i32>[n]) -> Vec<i32>[n])]
fn add(x: &Vec<i32>, y: &Vec<i32>) -> Vec<i32> {
    assert(x.len() == y.len());
    fill_vec_index(x.len(), |i| x[i] + y[i])
}
