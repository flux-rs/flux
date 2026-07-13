#![flux::defs {
    fn ptr_ok(p: ptr, num_bytes: int, align: int) -> bool {
        p.addr > 0 && p.addr >= p.base && num_bytes <= p.size && p.addr % align == 0
    }
}]

extern crate flux_core;

// --- copy ---

// src unaligned: ptr_ok requires alignment, but src is missing it
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    sp.addr > 0 && sp.addr >= sp.base && sp.size >= 4 &&
    ptr_ok(dp, 4, 4))]
pub fn test_copy_src_unaligned(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy(src, dst, 1) } //~ ERROR refinement type error
}

// dst unaligned
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    ptr_ok(sp, 4, 4) &&
    dp.addr > 0 && dp.addr >= dp.base && dp.size >= 4)]
pub fn test_copy_dst_unaligned(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy(src, dst, 1) } //~ ERROR refinement type error
}

// src too small: only 3 bytes available, but 4 needed
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    sp.addr > 0 && sp.addr >= sp.base && sp.size == 3 && sp.addr % 4 == 0 &&
    ptr_ok(dp, 4, 4))]
pub fn test_copy_src_too_small(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy(src, dst, 1) } //~ ERROR refinement type error
}

// dst too small
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    ptr_ok(sp, 4, 4) &&
    dp.addr > 0 && dp.addr >= dp.base && dp.size == 3 && dp.addr % 4 == 0)]
pub fn test_copy_dst_too_small(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy(src, dst, 1) } //~ ERROR refinement type error
}

// src null with nonzero count
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    sp.addr == 0 && ptr_ok(dp, 4, 4))]
pub fn test_copy_src_null(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy(src, dst, 1) } //~ ERROR refinement type error
}

// --- copy_nonoverlapping ---

// overlapping ranges: negation of nonoverlapping is provably true
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32, count: usize) requires
    ptr_ok(sp, count * 4, 4) && ptr_ok(dp, count * 4, 4) &&
    sp.addr < dp.addr + count * 4 && dp.addr < sp.addr + count * 4)]
pub fn test_copy_nonoverlapping_overlapping(src: *const u32, dst: *mut u32, count: usize) {
    unsafe { std::ptr::copy_nonoverlapping(src, dst, count) } //~ ERROR refinement type error
}

// src unaligned
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    sp.addr > 0 && sp.addr >= sp.base && sp.size >= 4 &&
    ptr_ok(dp, 4, 4) &&
    sp.addr + 4 <= dp.addr)]
pub fn test_copy_nonoverlapping_src_unaligned(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy_nonoverlapping(src, dst, 1) } //~ ERROR refinement type error
}

// dst too small
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    ptr_ok(sp, 4, 4) &&
    dp.addr > 0 && dp.addr >= dp.base && dp.size == 3 && dp.addr % 4 == 0 &&
    sp.addr + 4 <= dp.addr)]
pub fn test_copy_nonoverlapping_dst_too_small(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy_nonoverlapping(src, dst, 1) } //~ ERROR refinement type error
}
