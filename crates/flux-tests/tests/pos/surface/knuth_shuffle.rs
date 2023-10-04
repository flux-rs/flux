// Based on Prusti test/example

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn(lo: usize, hi: usize{lo < hi}) -> usize{v: lo <= v && v < hi})]
fn gen_range(low: usize, _high: usize) -> usize {
    low
}

#[flux::sig(fn(&mut RVec<i32>[@n]) -> usize)]
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
