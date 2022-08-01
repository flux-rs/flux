#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(Box<i32[@n]>) -> i32[n+1])]
pub fn inc(b: Box<i32>) -> i32 {
    let x = *b;
    x + 2 //~ ERROR postcondition
}
