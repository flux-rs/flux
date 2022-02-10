#![feature(register_tool)]
#![register_tool(lr)]

// Test of `mod` support
// Uses usize instead of i32 to avoid subtleties with negative numbers
#[lr::ty(fn(usize{x: x % 2 == 1}) -> usize{y: y == 1})]
pub fn input_must_be_odd(a: usize) -> usize {
    a % 2
}

pub fn test_mod() {
    input_must_be_odd(3);
    input_must_be_odd(5);
    input_must_be_odd(27);
}

#[lr::ty(fn(bool{x: x == true}) -> bool{y: y == true})]
pub fn must_be_true(a: bool) -> bool {
    a && true
}

pub fn test_and() {
    must_be_true(true);
    must_be_true(5 == 5);
}

#[lr::ty(fn<a: int{a >= 0}, b: int{b >= 0}>(i32{x: x == a}, i32{y: y == b}) -> i32{z: z == a % b})]
pub fn mod_signed_pos(a: i32, b: i32) -> i32 {
    a % b
}