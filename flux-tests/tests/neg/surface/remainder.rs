#![feature(register_tool)]
#![register_tool(flux)]

// Test of `mod` support
// usize preserves mod semantics
#[flux::sig(fn(a: usize{a % 2 == 1}) -> usize[1])]
pub fn input_must_be_odd(a: usize) -> usize {
    a % 2
}

#[flux::sig(fn() -> usize)]
pub fn test_mod() -> usize {
    input_must_be_odd(3);
    input_must_be_odd(5);
    input_must_be_odd(24); //~ ERROR precondition might not hold
    0
}

// Error because a and b may be < 0 and which doesn't preserve mod semantics
#[flux::sig(fn(a: i32, b: i32) -> i32[a % b])]
pub fn mod_signed(a: i32, b: i32) -> i32 { //~ ERROR postcondition might not hold
    a % b
}
