#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(x: i32) -> i32{v: x < v})]
pub fn inc(x: i32) -> i32 {
    x + 1
}
