#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(x: i32) -> i32{v: x < v})]
pub fn double(x: i32) -> i32 { //~ ERROR postcondition might not hold
    x + x
}
