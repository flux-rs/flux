extern crate flux_core;

use std::ptr::NonNull;

#[flux::spec(fn(NonNull<u8>{p: p.addr > 1}))]
fn needs_above_one(_p: NonNull<u8>) {}

// A `NonNull` address is positive, but nothing more.
pub fn test_nonnull_not_above_one(p: NonNull<u8>) {
    needs_above_one(p); //~ ERROR refinement type error
}
