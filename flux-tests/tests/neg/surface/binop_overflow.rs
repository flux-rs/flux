// ignore-test
// TODO: Uncomment when we can set flags on a per-test basis. Add the ERROR
// overflow comment on the lines too.
#![feature(register_tool)]
#![register_tool(flux)]

// Arithmetic BinOps
// These check for over/underflow
#[flux::sig(fn(a: u32, b: u32) -> u32{v: v == a - b})]
pub fn uint_sub(a: u32, b: u32) -> u32 {
    a - b //~ ERROR overflow
}

#[flux::sig(fn(a: u32, b: u32) -> u32{v: v == a + b})]
pub fn uint_add(a: u32, b: u32) -> u32 {
    a + b //~ ERROR overflow
}

#[flux::sig(fn(a: i32{a > 0}, b: i32{b > 0}) -> i32{v: v == a + b})]
pub fn uint_add_pos(a: i32, b: i32) -> i32 {
    a + b //~ ERROR overflow
}

#[flux::sig(fn(a: i32{a < 0}, b: i32{b < 0}) -> i32{v: v == a + b})]
pub fn uint_add_neg(a: i32, b: i32) -> i32 {
    a + b //~ ERROR overflow
}
