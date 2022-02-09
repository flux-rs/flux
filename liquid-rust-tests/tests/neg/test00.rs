#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn<n: int>(i32@n) -> i32{v: v < n})]
pub fn inc(x: i32) -> i32 {
    x + 1
}
// ~^ ERROR the postcondition in this function might not hold
