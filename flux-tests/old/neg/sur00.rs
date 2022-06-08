#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(x: i32) -> i32{v: v < x})]
pub fn inc(x: i32) -> i32 { //~ ERROR postcondition might not hold
    x + 1
}
