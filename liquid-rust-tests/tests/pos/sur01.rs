#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(x: n@i32) -> i32{v: n < v})]
pub fn inc(x: i32) -> i32 {
    x + 1
}
