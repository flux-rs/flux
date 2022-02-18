#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(x @ i32{0 < x}) -> i32{v: x < v})]
pub fn double(x: i32) -> i32 {
    x + x
}
