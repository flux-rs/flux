#![allow(unused)]

fn id<T>(x: T) -> T {
    x
}

#[flux::sig(fn(c: Option<usize[99]>) -> Option<usize[100]>)]
pub fn test_fail(c: Option<usize>) -> Option<usize> {
    c.map(id) //~ ERROR refinement type
}

#[flux::sig(fn(Option<i32[99]>) -> Option<i32[100]>)]
fn test_also_ok(x: Option<i32>) -> Option<i32> {
    let f = id;
    x.map(f) //~ ERROR refinement type
}
