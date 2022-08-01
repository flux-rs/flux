#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(Box<i32[@n]>) -> i32[n+1])]
pub fn inc(b: Box<i32>) -> i32 {
    let x = *b;
    x + 1
}

#[flux::sig(fn(Box<i32[@n]>) -> Box<i32[n+1]>)]
pub fn inc_box(b: Box<i32>) -> Box<i32> {
    let x = *b;
    Box::new(x + 1)
}

#[flux::sig(fn(n:i32) -> i32[n+1])]
pub fn inc_test(n: i32) -> i32 {
    let b0 = Box::new(n);
    let b1 = inc_box(b0);
    *b1
}
