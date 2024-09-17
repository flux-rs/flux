#![allow(unused)]

fn id<T>(x: T) -> T {
    x
}

#[flux::sig(fn(c: Option<usize[99]>) -> Option<usize[99]>)]
pub fn test_ok(c: Option<usize>) -> Option<usize> {
    c.map(id)
}
