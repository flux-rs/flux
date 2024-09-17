#![allow(unused)]

#[flux::sig(fn (x:usize) -> usize[x+1])]
fn inc(x: usize) -> usize {
    x + 1
}

#[flux::sig(fn(c: Option<usize[99]>) -> Option<usize[100]>)]
pub fn test_ok(c: Option<usize>) -> Option<usize> {
    c.map(inc)
}

