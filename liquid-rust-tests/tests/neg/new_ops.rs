#![feature(register_tool)]
#![register_tool(lr)]

// Test of `mod` support
// Uses usize instead of i32 to avoid subtleties with negative numbers
#[lr::ty(fn(usize{x: x % 2 == 1}) -> usize{y: y == 1})]
pub fn input_must_be_odd(a: usize) -> usize {
    a % 2
}

#[lr::ty(fn() -> usize)]
pub fn test_mod() -> usize {
    input_must_be_odd(3);
    input_must_be_odd(5);
    input_must_be_odd(24);
    0
}

#[lr::ty(fn(bool{x: x == true}) -> bool{y: y == true})]
pub fn must_be_true(a: bool) -> bool {
    a && true
}

#[lr::ty(fn() -> usize)]
pub fn test_and() -> usize {
    must_be_true(true);
    must_be_true(5 == 6);
    0
}

// Unsafe because a and b may be < 0
#[lr::ty(fn<a: int, b: int>(i32{x: x == a}, i32{y: y == b}) -> i32{z: z == a % b})]
pub fn mod_signed(a: i32, b: i32) -> i32 {
    a % b
}