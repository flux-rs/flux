#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::cfg(scrape_quals = true)]

// test that the (fixpoint) `--scrape` mechanism suffices to get
// the qualifier needed for the loop invariant below.

#[flux::sig(fn(lo: usize, hi:usize{lo<=hi}) -> usize[hi-lo] )]
pub fn test_ix(lo: usize, hi: usize) -> usize {
    let mut i = lo;
    let mut res = 0;
    while i < hi {
        // inv: res = i - lo
        res += 1;
        i += 1;
    }
    res
}

#[flux::sig(fn(lo: usize, hi:usize{lo<=hi}) -> usize{v: v == hi-lo} )]
pub fn test_ex(lo: usize, hi: usize) -> usize {
    let mut i = lo;
    let mut res = 0;
    while i < hi {
        // inv: res = i - lo
        res += 1;
        i += 1;
    }
    res
}
