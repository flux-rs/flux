// https://github.com/flux-rs/flux/issues/1010

use flux_rs::{attrs::*, bitvec::BV32};

#[sig(fn (x:BV32{x == 1}) ensures (x << 3 == 9))]
pub fn test_shl_b_err(_x: BV32) {} //~ ERROR refinement type

#[sig(fn (x:BV32{x == 8}) ensures (x >> 3 == 2))]
pub fn test_shr_b_err(_x: BV32) {} //~ ERROR refinement type

#[sig(fn (x:BV32{x == 8}) ensures (x | 3 == 12))]
pub fn test_or_b_err(_x: BV32) {} //~ ERROR refinement type

#[sig(fn (x:BV32{x == 10}) ensures (x & 3 == 20))]
pub fn test_and_b_err(_x: BV32) {} //~ ERROR refinement type
