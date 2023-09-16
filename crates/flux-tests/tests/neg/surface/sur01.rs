#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x: i32) -> i32{v: x < v})]
pub fn double(x: i32) -> i32 {
    x + x //~ ERROR refinement type error
}
