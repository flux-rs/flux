#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::trusted]
#[flux::sig(fn(lo: usize, hi:usize{lo < hi}) -> RVec<usize{v:lo<=v && v<hi}>[hi-lo])]
pub fn range(lo: usize, hi: usize) -> RVec<usize> {
    let mut i = lo;
    let mut res = RVec::new();
    while i < hi {
        res.push(i);
        i += 1;
    }
    res
}

#[flux::sig(fn(a: { &RVec<f32>[@k] | 0 < k}) -> usize{v: v < k})]
pub fn min_index_fold(a: &RVec<f32>) -> usize {
    range(0, a.len()).fold(0, |min, i| if a[*i] < a[min] { *i } else { min })
}
