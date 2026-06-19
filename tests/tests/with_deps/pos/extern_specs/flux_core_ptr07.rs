#![flux::defs {
    fn ptr_ok(p: ptr, num_bytes: int, align: int) -> bool {
        p.addr > 0 && p.addr >= p.base && num_bytes <= p.size && p.addr % align == 0
    }
}]

extern crate flux_core;

// --- copy ---

#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    ptr_ok(sp, 8, 4) && ptr_ok(dp, 8, 4))]
pub fn test_copy_concrete(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy(src, dst, 2) }
}

// zero count: only alignment required; null is fine for validity
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    sp.addr % 4 == 0 && dp.addr % 4 == 0)]
pub fn test_copy_zero_count(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy(src, dst, 0) }
}

#[flux::spec(fn (src: *const[@sp] T, dst: *mut[@dp] T) requires
    T::size_of() > 0 &&
    ptr_ok(sp, T::size_of(), T::align_of()) &&
    ptr_ok(dp, T::size_of(), T::align_of()))]
pub fn test_copy_one<T>(src: *const T, dst: *mut T) {
    unsafe { std::ptr::copy(src, dst, 1) }
}

// --- copy_nonoverlapping ---

// dst starts after src ends
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    ptr_ok(sp, 8, 4) && ptr_ok(dp, 8, 4) && sp.addr + 8 <= dp.addr)]
pub fn test_copy_nonoverlapping_after(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy_nonoverlapping(src, dst, 2) }
}

// src starts after dst ends
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    ptr_ok(sp, 8, 4) && ptr_ok(dp, 8, 4) && dp.addr + 8 <= sp.addr)]
pub fn test_copy_nonoverlapping_before(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy_nonoverlapping(src, dst, 2) }
}

// zero count: nonoverlapping is trivially true; only alignment required
#[flux::spec(fn (src: *const[@sp] u32, dst: *mut[@dp] u32) requires
    sp.addr % 4 == 0 && dp.addr % 4 == 0)]
pub fn test_copy_nonoverlapping_zero_count(src: *const u32, dst: *mut u32) {
    unsafe { std::ptr::copy_nonoverlapping(src, dst, 0) }
}

#[flux::spec(fn (src: *const[@sp] T, dst: *mut[@dp] T) requires
    T::size_of() > 0 &&
    ptr_ok(sp, T::size_of(), T::align_of()) &&
    ptr_ok(dp, T::size_of(), T::align_of()) &&
    sp.addr + T::size_of() <= dp.addr)]
pub fn test_copy_nonoverlapping_one<T>(src: *const T, dst: *mut T) {
    unsafe { std::ptr::copy_nonoverlapping(src, dst, 1) }
}
