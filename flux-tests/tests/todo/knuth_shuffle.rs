// Based on Prusti test/example

#![feature(register_tool)]
#![register_tool(flux)]

#[path = "lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::assume]
#[flux::sig(fn(lo: usize, hi: usize{lo < hi}) -> usize{x: lo <= x && x < hi})]
fn gen_range(_low: usize, _high: usize) -> usize {
    unimplemented!();
}

// This only work if we annotate it like `&mut RVec<i32>[@n]`
#[flux::sig(fn(v: &mut RVec<i32>))]
pub fn knuth_shuffle(v: &mut RVec<i32>) {
    let l = v.len();

    let mut n = 0;
    let bgn = 0;
    while n < l {
        let i = gen_range(bgn, l - n);
        v.swap(i, l - n - 1);
        n += 1;
    }
}
