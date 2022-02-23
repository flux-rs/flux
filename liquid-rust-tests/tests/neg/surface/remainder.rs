#![feature(register_tool)]
#![register_tool(lr)]

// Test of `mod` support
// usize preserves mod semantics
#[lr::sig(fn(a:usize{a % 2 == 1}) -> usize{y: y == 1})]
pub fn input_must_be_odd(a: usize) -> usize {
    a % 2
}

#[lr::sig(fn() -> usize)]
pub fn test_mod() -> usize {
    input_must_be_odd(3);
    input_must_be_odd(5);
    input_must_be_odd(24); //~ ERROR precondition might not hold
    0
}

// Error because a and b may be < 0 and which doesn't preserve mod semantics
#[lr::sig(fn(a:i32, b:i32) -> i32{z: z == a % b})]
pub fn mod_signed(a: i32, b: i32) -> i32 { //~ ERROR postcondition might not hold
    a % b
}
