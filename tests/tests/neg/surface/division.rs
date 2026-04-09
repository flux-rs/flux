// Tests for integer division with signed integers
// For signed integers, the result is only constrained when both operands are non-negative.
// When either operand is negative, the result is unconstrained because Rust truncates
// toward zero while SMT-LIB's `div` floors (for positive divisors), so they diverge.

// UNSOUND BEFORE FIX: Flux used to verify this as returning `bool[true]`, but it actually
// returns `false` because Rust computes -7/2 = -3, not -4.
// After the fix, this should be rejected because the result of `-7_i32 / 2` is
// unconstrained (since the dividend is negative).
#[flux::sig(fn() -> bool[true])]
pub fn div_unsound() -> bool {
    let x = -7_i32 / 2;
    x == -4 //~ ERROR refinement type error
}

// Error because `a` may be negative, which doesn't preserve SMT-LIB div semantics
#[flux::sig(fn(a: i32, b: i32{b > 0}) -> i32[a/b])]
pub fn div_signed_unconstrained(a: i32, b: i32) -> i32 {
    a / b //~ ERROR refinement type error
}
