extern crate flux_core;

use std::ptr::NonNull;

// --- cast ---

// The cast preserves `size`, so widening does not conjure up bytes: only 4 are known
// accessible and an `i64` read needs 8. The address is already 8-byte aligned.
#[flux::spec(fn({NonNull<i32>[@base, @addr, @size] | base == addr && size == 4 && addr % 8 == 0}))]
pub fn test_cast_widen_read(nn: NonNull<i32>) {
    let wide: NonNull<i64> = nn.cast();
    unsafe {
        let _v = wide.read(); //~ ERROR refinement type
    }
}

// Nor alignment: a byte pointer is only known to be 1-byte aligned, so an `i32` read
// cannot establish `addr % 4 == 0`.
#[flux::spec(fn({NonNull<u8>[@base, @addr, @size] | base == addr && size >= 4}))]
pub fn test_cast_align(nn: NonNull<u8>) {
    let ints: NonNull<i32> = nn.cast();
    unsafe {
        let _v = ints.read(); //~ ERROR refinement type
    }
}
