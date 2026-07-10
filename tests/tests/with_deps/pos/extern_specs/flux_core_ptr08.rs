#![flux::defs {
    fn ptr_ok(p: ptr, num_bytes: int, align: int) -> bool {
        p.addr > 0 && p.addr >= p.base && num_bytes <= p.size && p.addr % align == 0
    }
}]

extern crate flux_core;

// --- swap ---

#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    ptr_ok(xp, 4, 4) && ptr_ok(yp, 4, 4))]
pub fn test_swap_concrete(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap(x, y) }
}

#[flux::spec(fn (x: *mut[@xp] T, y: *mut[@yp] T) requires
    T::size_of() > 0 &&
    ptr_ok(xp, T::size_of(), T::align_of()) &&
    ptr_ok(yp, T::size_of(), T::align_of()))]
pub fn test_swap_generic<T>(x: *mut T, y: *mut T) {
    unsafe { std::ptr::swap(x, y) }
}

// --- swap_nonoverlapping ---

// x ends before y starts
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    ptr_ok(xp, 8, 4) && ptr_ok(yp, 8, 4) && xp.addr + 8 <= yp.addr)]
pub fn test_swap_nonoverlapping_after(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap_nonoverlapping(x, y, 2) }
}

// y ends before x starts
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    ptr_ok(xp, 8, 4) && ptr_ok(yp, 8, 4) && yp.addr + 8 <= xp.addr)]
pub fn test_swap_nonoverlapping_before(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap_nonoverlapping(x, y, 2) }
}

// zero count: nonoverlapping trivially true; only alignment required
#[flux::spec(fn (x: *mut[@xp] u32, y: *mut[@yp] u32) requires
    xp.addr % 4 == 0 && yp.addr % 4 == 0)]
pub fn test_swap_nonoverlapping_zero_count(x: *mut u32, y: *mut u32) {
    unsafe { std::ptr::swap_nonoverlapping(x, y, 0) }
}

#[flux::spec(fn (x: *mut[@xp] T, y: *mut[@yp] T) requires
    T::size_of() > 0 &&
    ptr_ok(xp, T::size_of(), T::align_of()) &&
    ptr_ok(yp, T::size_of(), T::align_of()) &&
    xp.addr + T::size_of() <= yp.addr)]
pub fn test_swap_nonoverlapping_generic<T>(x: *mut T, y: *mut T) {
    unsafe { std::ptr::swap_nonoverlapping(x, y, 1) }
}
