#![feature(register_tool)]
#![register_tool(flux)]

#[flux::ty(fn<n: int>(i32@n) -> i32{v: v > n})]
pub fn inc(x: i32) -> i32 {
    x + 1
}
