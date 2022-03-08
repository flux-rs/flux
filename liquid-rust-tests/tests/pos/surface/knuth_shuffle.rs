// Based on Prusti test/example

#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/surface/rvec.rs"]
mod rvec;
use rvec::RVec;

#[lr::assume]
#[lr::ty(fn<lo: int, hi: int{lo < hi}>(usize@lo, usize@hi) -> usize{x: lo <= x && x < hi})]
fn gen_range(low: usize, _high: usize) -> usize {
    low
}


#[lr::ty(fn<n: int>(v: RVec<i32>@n; ref<v>) -> usize; v: RVec<i32>@n)]
pub fn knuth_shuffle(v: &mut RVec<i32>) -> usize {
    let l = v.len();

    let mut n = 0;
    let bgn = 0;
    while n < l {
        let i = gen_range(bgn, l - n);
        v.swap(i, l - n - 1);
        n += 1;
    }

    0
}