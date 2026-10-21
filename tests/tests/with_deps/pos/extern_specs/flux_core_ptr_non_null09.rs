extern crate flux_core;

use std::ptr::NonNull;

#[flux::spec(fn(NonNull<u8>{p: p.addr > 0 && p.base >= 0 && p.addr <= usize::MAX && p.addr + p.size <= usize::MAX}))]
fn needs_bounds(_p: NonNull<u8>) {}

#[flux::spec(fn(*mut{p: p.addr > 0} u8))]
fn needs_positive_raw(_p: *mut u8) {}

// A `NonNull` address is positive, not just non-zero, and its allocation fits in the address space.
pub fn test_nonnull_bounds(p: NonNull<u8>) {
    needs_bounds(p);
}

// ... and its address stays positive after converting to a raw pointer.
pub fn test_nonnull_as_ptr_positive(p: NonNull<u8>) {
    needs_positive_raw(p.as_ptr());
}
