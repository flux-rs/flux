// https://github.com/flux-rs/flux/issues/1010

use flux_rs::{attrs::*, bitvec::BV8};

#[sig(fn (x:u8[1], y:u8[2]) -> u8[3])]
pub fn test_to_bv8(x: u8, y: u8) -> u8 {
    let bv_x = BV8::from(x);
    let bv_y = BV8::from(y);
    let result = bv_x + bv_y;
    result.into()
}

#[sig(fn (x:BV8{x == 1}) ensures (bv_shl(x, 3) == 8))]
pub fn test_shl_a(_x: BV8) {}

#[sig(fn (x:BV8{x == 1}) ensures (x << 2 == 4))]
pub fn test_shl_b(_x: BV8) {}

#[sig(fn (x:BV8{x == 4}) ensures (bv_lshr(x, 2) == 1))]
pub fn test_shr_a(_x: BV8) {}

#[sig(fn (x:BV8{x == 4}) ensures (x >> 2 == 1))]
pub fn test_shr_b(_x: BV8) {}

#[sig(fn (x:BV8{x == 4}) ensures (bv_or(x, 1) == 5))]
pub fn test_or_a(_x: BV8) {}

#[sig(fn (x:BV8{x == 4}) ensures (x | 3 == 7))]
pub fn test_or_b(_x: BV8) {}

#[sig(fn (x:BV8{x == 6}) ensures (bv_and(x, 3) == 2))]
pub fn test_and_a(_x: BV8) {}

#[sig(fn (x:BV8{x == 6}) ensures (x & 3 == 2))]
pub fn test_and_b(_x: BV8) {}

#[sig(fn (x:BV8{x == 6}) ensures (bv_xor(x, 3) == 5))]
pub fn test_xor_a(_x: BV8) {}

#[sig(fn (x:BV8{x == 6}) ensures (x ^ 3 == 5))]
pub fn test_xor_b(_x: BV8) {}
