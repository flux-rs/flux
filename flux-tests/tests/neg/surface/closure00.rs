#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(c: Option<bool>) -> Option<i32{v:10 <= v}>)]
pub fn test0(c: Option<bool>) -> Option<i32> {
    c.map(|b| if b { 1 } else { 2 }) //~ ERROR: refinement type
}

#[flux::sig(fn(c: Option<bool>) -> Option<i32[1]>)]
pub fn test2(c: Option<bool>) -> Option<i32> {
    c.map(|b| if b { 1 } else { 2 }) //~ ERROR: refinement type
}

#[flux::sig(fn(n:usize) -> usize[n + 3])]
fn test3(n: usize) -> usize {
    checked_add(n, 1)
        .and_then(|m| Some(m + 1))
        .expect("overflow") //~ ERROR: refinement type
}

#[flux::trusted]
#[flux::sig(fn(n:usize, m:usize) -> Option<usize[n + m]>)]
fn checked_add(n: usize, m: usize) -> Option<usize> {
    n.checked_add(m)
}
