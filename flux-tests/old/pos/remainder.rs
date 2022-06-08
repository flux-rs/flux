#![feature(register_tool)]
#![register_tool(flux)]

// Test of `mod` support
// Uses usize instead of i32 to avoid subtleties with negative numbers
#[flux::ty(fn(usize{x: x % 2 == 1}) -> usize{y: y == 1})]
pub fn input_must_be_odd(a: usize) -> usize {
    a % 2
}

#[flux::ty(fn() -> i32)]
pub fn test_mod() -> i32 {
    input_must_be_odd(3);
    input_must_be_odd(5);
    input_must_be_odd(27);
    0
}

#[flux::ty(fn<a: int{a >= 0}, b: int{b >= 0}>(i32{x: x == a}, i32{y: y == b}) -> i32{z: z == a % b})]
pub fn mod_signed_pos(a: i32, b: i32) -> i32 {
    a % b
}
