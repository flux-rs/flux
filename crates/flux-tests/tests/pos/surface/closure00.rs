#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(c: Option<bool>) -> Option<i32{v:0 <= v}>)]
pub fn test0(c: Option<bool>) -> Option<i32> {
    c.map(|b| if b { 1 } else { 2 })
}

#[flux::sig(fn(c: Option<bool>) -> Option<i32{v:1 <= v}>)]
pub fn test1(c: Option<bool>) -> Option<i32> {
    c.map(|b| if b { 1 } else { 2 })
}

#[flux::sig(fn(c: Option<bool[true]>) -> Option<i32[1]>)]
pub fn test2(c: Option<bool>) -> Option<i32> {
    c.map(|b| if b { 1 } else { 2 })
}

#[flux::sig(fn(n:usize) -> usize[n + 2])]
pub fn test3(n: usize) -> usize {
    checked_add(n, 1)
        .and_then(|m| Some(m + 1))
        .expect("overflow")
}

#[flux::trusted]
#[flux::sig(fn(n:usize, m:usize) -> Option<usize[n + m]>)]
pub fn checked_add(n: usize, m: usize) -> Option<usize> {
    n.checked_add(m)
}
