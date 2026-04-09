// Tests for integer division
// For unsigned integers, Rust's truncating division agrees with SMT-LIB's Euclidean `div`
// because both operands are non-negative.
// For signed integers, the result is only constrained when both operands are non-negative.

// Unsigned division: always exact
#[flux::sig(fn(a: u32, b: u32{b > 0}) -> u32[a/b])]
pub fn div_unsigned(a: u32, b: u32) -> u32 {
    a / b
}

// Signed division: exact when both operands are non-negative
#[flux::sig(fn(a: i32{a >= 0}, b: i32{b > 0}) -> i32[a/b])]
pub fn div_signed_nonneg(a: i32, b: i32) -> i32 {
    a / b
}
