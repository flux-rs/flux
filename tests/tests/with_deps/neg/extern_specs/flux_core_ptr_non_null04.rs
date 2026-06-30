extern crate flux_core;

use std::ptr::NonNull;

// --- offset_from ---

// different allocations: sbase != obase violates same-allocation requirement.
// Alignment is constrained so only the base check fails.
#[flux::spec(fn (p: NonNull<i32>[@sbase, @saddr, @ssize], q: NonNull<i32>[@obase, @oaddr, @osize])
    requires saddr >= sbase && ssize >= 0 && oaddr >= obase && osize >= 0 && obase != sbase && (saddr - oaddr) % 4 == 0)]
pub fn test_offset_from_diff_base(p: NonNull<i32>, q: NonNull<i32>) {
    unsafe {
        let _ = p.offset_from(q); //~ ERROR refinement type error
    }
}

// non-element-aligned distance: q is 1 byte ahead of p, but T = i32 requires a multiple of 4
#[flux::spec(fn (p: NonNull<i32>[@sbase, @saddr, @ssize], q: NonNull<i32>[@obase, @oaddr, @osize])
    requires sbase == obase && saddr >= sbase && ssize >= 0 && oaddr == saddr + 1 && osize >= 0)]
pub fn test_offset_from_unaligned(p: NonNull<i32>, q: NonNull<i32>) {
    unsafe {
        let _ = q.offset_from(p); //~ ERROR refinement type error
    }
}

// ZST: size_of::<()>() == 0, violating T::size_of() > 0
#[flux::spec(fn (p: NonNull<()>[@sbase, @saddr, @ssize], q: NonNull<()>[@obase, @oaddr, @osize])
    requires sbase == obase && saddr >= sbase && ssize >= 0 && oaddr == saddr && osize == ssize)]
pub fn test_offset_from_zst(p: NonNull<()>, q: NonNull<()>) {
    unsafe {
        let _ = p.offset_from(q); //~ ERROR refinement type error
    }
}

// --- offset_from_unsigned ---

// origin is ahead of self: violates saddr >= oaddr.
// oaddr = saddr + 4 ensures (saddr - oaddr) % 4 == 0 in SMT-lib.
#[flux::spec(fn (p: NonNull<i32>[@sbase, @saddr, @ssize], q: NonNull<i32>[@obase, @oaddr, @osize])
    requires sbase == obase && saddr >= sbase && ssize >= 0 && oaddr == saddr + 4 && osize >= 0)]
pub fn test_offset_from_unsigned_reversed(p: NonNull<i32>, q: NonNull<i32>) {
    unsafe {
        let _ = p.offset_from_unsigned(q); //~ ERROR refinement type error
    }
}

// --- slice_from_raw_parts ---

// 5 elements × 4 bytes = 20 bytes exceeds the 16-byte buffer; requires fails
pub fn test_slice_from_raw_parts_oob(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    let _slice_nn = NonNull::slice_from_raw_parts(nn, 5); //~ ERROR refinement type error
}
