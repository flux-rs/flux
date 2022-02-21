#![feature(register_tool)]
#![register_tool(lr)]

// Test of `mod` support
// Uses usize instead of i32 to avoid subtleties with negative numbers
#[lr::sig(fn(a:usize{a % 2 == 1}) -> usize{y: y == 1})]
pub fn input_must_be_odd(a: usize) -> usize {
    a % 2
}

#[lr::sig(fn() -> i32)]
pub fn test_mod() -> i32 {
    input_must_be_odd(3);
    input_must_be_odd(5);
    input_must_be_odd(27);
    0
}

#[lr::sig(fn(a:i32{0 <= a}, b:i32{0 <= b}) -> i32{z: z == a % b})]
pub fn mod_signed_pos(a: i32, b: i32) -> i32 {
    a % b
}
