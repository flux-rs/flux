#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::cfg(scrape_quals = "true")]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

// test that the (fixpoint) `--scrape` mechanism suffices to get
// the qualifier needed for the loop invariant below.

#[flux::sig(fn(lo: usize, hi:usize{lo<=hi}) -> RVec<usize>[hi-lo] )]
pub fn range(lo: usize, hi: usize) -> RVec<usize> {
    let mut i = lo;
    let mut res = RVec::new();
    while i < hi {
        // inv: res.len() = i - lo
        res.push(i);
        i += 1;
    }
    res
}
