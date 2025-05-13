#![feature(step_trait, allocator_api)]
#![allow(unused)]

#[path = "../../lib/iterator.rs"]
mod iterator;

#[path = "../../lib/vec.rs"]
mod vec;

#[flux_rs::sig(fn (bool[true]))]
pub fn assert(b: bool) {}

#[flux_rs::sig(fn (vec: &Vec<A>[@n], f: F)
               where F: FnMut(usize{v:v < n}, &A) -> i32)]
pub fn for_each<F, A>(vec: &Vec<A>, mut f: F)
where
    F: FnMut(usize, &A) -> i32,
{
    let n = vec.len();
    for i in 0..n {
        f(i, &vec[i]);
    }
}

#[flux_rs::sig(fn (vec1: &Vec<_>[@n], vec2: &Vec<_>[n]) -> f64)]
pub fn dot_product_iter(vec1: &Vec<f64>, vec2: &Vec<f64>) -> f64 {
    let mut res = 0.0;
    for_each(&vec1, |i, v| {
        res += v * vec2[i];
        0
    });
    res
}

#[flux_rs::sig(fn (vec1: &Vec<_>[@n], vec2: &Vec<_>[n]) -> f64)]
pub fn dot_product_loop(vec1: &Vec<f64>, vec2: &Vec<f64>) -> f64 {
    let n = vec1.len();
    let mut res = 0.0;
    for i in 0..n {
        res += vec1[i] * vec2[i];
    }
    res
}
