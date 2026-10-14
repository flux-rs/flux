#![allow(unused)]
#![feature(allocator_ext, try_trait_v2)]

#[path = "../../lib/parametric_std.rs"]
mod parametric_std;


#[flux::sig(fn (x:usize) -> usize[x+1])]
fn inc(x: usize) -> usize {
    x + 1
}

#[flux::sig(fn(c: Option<usize[99]>) -> Option<usize[100]>)]
pub fn test_ok(c: Option<usize>) -> Option<usize> {
    c.map(inc)
}
