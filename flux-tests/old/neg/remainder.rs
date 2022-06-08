#![feature(register_tool)]
#![register_tool(flux)]

// Test of `mod` support
// usize preserves mod semantics
#[flux::ty(fn(usize{x: x % 2 == 1}) -> usize{y: y == 1})]
pub fn input_must_be_odd(a: usize) -> usize {
    a % 2
}

#[flux::ty(fn() -> usize)]
pub fn test_mod() -> usize {
    input_must_be_odd(3);
    input_must_be_odd(5);
    input_must_be_odd(24); //~ ERROR precondition might not hold
    0
}

// Error because a and b may be < 0 and which doesn't preserve mod semantics
#[flux::ty(fn<a: int, b: int>(i32{x: x == a}, i32{y: y == b}) -> i32{z: z == a % b})]
pub fn mod_signed(a: i32, b: i32) -> i32 {
    //~ ERROR postcondition might not hold
    a % b
}
