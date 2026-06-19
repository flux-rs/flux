#![flux::defs {
    fn ptr_ok(p: ptr, num_bytes: int, align: int) -> bool {
        p.addr > 0 && p.addr >= p.base && num_bytes <= p.size && p.addr % align == 0
    }
}]

extern crate flux_core;

// --- swap ---

// x unaligned
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    xp.addr > 0 && xp.addr >= xp.base && xp.size >= 4 &&
    ptr_ok(yp, 4, 4))]
pub fn test_swap_x_unaligned(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap(x, y) } //~ ERROR refinement type error
}

// y too small: only 3 bytes available, but 4 needed
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    ptr_ok(xp, 4, 4) &&
    yp.addr > 0 && yp.addr >= yp.base && yp.size == 3 && yp.addr % 4 == 0)]
pub fn test_swap_y_too_small(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap(x, y) } //~ ERROR refinement type error
}

// x null with non-zero size type
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    xp.addr == 0 && ptr_ok(yp, 4, 4))]
pub fn test_swap_x_null(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap(x, y) } //~ ERROR refinement type error
}

// --- swap_nonoverlapping ---

// overlapping ranges
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32, count: usize) requires
    ptr_ok(xp, count * 4, 4) && ptr_ok(yp, count * 4, 4) &&
    xp.addr < yp.addr + count * 4 && yp.addr < xp.addr + count * 4)]
pub fn test_swap_nonoverlapping_overlapping(x: *mut u32, y: *mut u32, count: usize) {
    unsafe { std::ptr::swap_nonoverlapping(x, y, count) } //~ ERROR refinement type error
}

// x unaligned
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    xp.addr > 0 && xp.addr >= xp.base && xp.size >= 4 &&
    ptr_ok(yp, 4, 4) &&
    xp.addr + 4 <= yp.addr)]
pub fn test_swap_nonoverlapping_x_unaligned(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap_nonoverlapping(x, y, 1) } //~ ERROR refinement type error
}

// y too small
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    ptr_ok(xp, 4, 4) &&
    yp.addr > 0 && yp.addr >= yp.base && yp.size == 3 && yp.addr % 4 == 0 &&
    xp.addr + 4 <= yp.addr)]
pub fn test_swap_nonoverlapping_y_too_small(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap_nonoverlapping(x, y, 1) } //~ ERROR refinement type error
}
