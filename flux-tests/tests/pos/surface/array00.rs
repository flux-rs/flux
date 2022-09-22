#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> [i32{v : v > 0}; 2])]
pub fn array00() -> [i32; 2] {
    [0, 1]
}
