// https://github.com/flux-rs/flux/issues/1010

use flux_rs::{attrs::*, bitvec::BV32};

#[sig(fn (x:BV32{x == 1}) ensures (bv_shl(x, 3) == 8))]
pub fn test_shl_a(_x: BV32) {}

#[sig(fn (x:BV32{x == 1}) ensures (x << 3 == 8))]
pub fn test_shl_b(_x: BV32) {}

#[sig(fn (x:BV32{x == 8}) ensures (bv_lshr(x, 3) == 1))]
pub fn test_shr_a(_x: BV32) {}

#[sig(fn (x:BV32{x == 8}) ensures (x >> 3 == 1))]
pub fn test_shr_b(_x: BV32) {}

#[sig(fn (x:BV32{x == 8}) ensures (bv_or(x, 3) == 11))]
pub fn test_or_a(_x: BV32) {}

#[sig(fn (x:BV32{x == 8}) ensures (x | 3 == 11))]
pub fn test_or_b(_x: BV32) {}

#[sig(fn (x:BV32{x == 10}) ensures (bv_and(x, 3) == 2))]
pub fn test_and_a(_x: BV32) {}

#[sig(fn (x:BV32{x == 10}) ensures (x & 3 == 2))]
pub fn test_and_b(_x: BV32) {}
