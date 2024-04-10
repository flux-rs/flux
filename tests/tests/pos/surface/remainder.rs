// Test of `mod` support
// Uses usize instead of i32 to avoid subtleties with negative numbers
#[flux::sig(fn(usize{v : v % 2 == 1}) -> usize[1])]
pub fn input_must_be_odd(a: usize) -> usize {
    a % 2
}

#[flux::sig(fn() -> i32)]
pub fn test_mod() -> i32 {
    input_must_be_odd(3);
    input_must_be_odd(5);
    input_must_be_odd(27);
    0
}

#[flux::sig(fn(a: i32{a >= 0}, b: i32{b > 0}) -> i32[a % b])]
pub fn mod_signed_pos(a: i32, b: i32) -> i32 {
    a % b
}
