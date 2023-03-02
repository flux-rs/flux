// ignore-test
// TODO: Uncomment when we can set flags on a per-test basis
#![feature(register_tool)]
#![register_tool(flux)]

// Arithmetic BinOps
//
// These require a guarantee that the operation will not over/underflow.
//
#[flux::sig(fn(a:u32, b:u32{b < a}) -> u32{v: v == a - b})]
pub fn uint_sub(a: u32, b: u32) -> u32 {
    a - b
}

#[flux::sig(fn(a:i32, b:i32{b + a > 0 && b + a < 1000000000}) -> i32{v: v == a + b})]
pub fn int_add(a: i32, b: i32) -> i32 {
    a + b
}
