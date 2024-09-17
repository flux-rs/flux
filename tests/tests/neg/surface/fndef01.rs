#![allow(unused)]

fn id<T>(x: T) -> T {
    x
}

#[flux::sig(fn(c: Option<usize[99]>) -> Option<usize[100]>)]
pub fn test_fail(c: Option<usize>) -> Option<usize> {
    c.map(id) //~ ERROR refinement type
}
