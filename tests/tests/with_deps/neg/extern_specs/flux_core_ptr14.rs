extern crate flux_core;

// The result of a wrapping operation may be out of bounds.
#[flux::spec(fn(ptr: *const[@p] u8) requires p.size == 1 && p.addr >= p.base && p.addr > 0)]
pub fn test_out_of_bounds(ptr: *const u8) {
    let q = ptr.wrapping_add(1);
    let _ = unsafe { std::ptr::read(q) }; //~ ERROR refinement type error
}

// Offsets that overflow the address space wrap around.
#[flux::spec(fn(ptr: *const[@p] u64, n: usize) -> *const{q: q.addr == p.addr + 8 * n} u64
    requires n > usize::MAX / 8)]
pub fn test_large_offset(ptr: *const u64, n: usize) -> *const u64 {
    ptr.wrapping_add(n) //~ ERROR refinement type error
}

// Wrapping keeps the address within `usize`, so it is not plain subtraction.
#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.addr == p.addr - 16} u8
    requires p.addr < 16)]
pub fn test_wraps(ptr: *const u8) -> *const u8 {
    ptr.wrapping_byte_sub(16) //~ ERROR refinement type error
}

// Moving before the start of the allocation is also out of bounds.
#[flux::spec(fn(ptr: *mut[@p] u8) requires p.addr == p.base && p.size >= 1 && p.addr > 1)]
pub fn test_before_start(ptr: *mut u8) {
    let q = ptr.wrapping_sub(1);
    unsafe { std::ptr::write(q, 0) }; //~ ERROR refinement type error
}

// The result keeps the allocation of `x`, so it cannot be used to access `y`, even
// at `y`'s address.
#[flux::spec(fn(x: *const[@p] u8, y: *const[@r] u8)
    requires p.addr == p.base && p.size == 1 && p.addr > 0 && r.addr == p.addr + 8)]
pub fn test_keeps_allocation(x: *const u8, _y: *const u8) {
    let z = x.wrapping_byte_offset(8);
    let _ = unsafe { std::ptr::read(z) }; //~ ERROR refinement type error
}

// Element offsets are scaled by the element size.
#[flux::spec(fn(ptr: *const[@p] u32) -> *const{q: q.addr == p.addr + 1} u32
    requires p.addr + 4 <= usize::MAX)]
pub fn test_element_size(ptr: *const u32) -> *const u32 {
    ptr.wrapping_add(1) //~ ERROR refinement type error
}

// The result may be null.
#[flux::spec(fn(ptr: *mut[@p] u8, n: usize) requires p.addr > 0)]
pub fn test_may_be_null(ptr: *mut u8, n: usize) {
    let _ = unsafe { std::ptr::NonNull::new_unchecked(ptr.wrapping_byte_sub(n)) }; //~ ERROR refinement type error
}

// Moving the pointer changes the number of bytes left in the allocation.
#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.size == p.size} u8 requires p.addr < usize::MAX)]
pub fn test_size_changes(ptr: *const u8) -> *const u8 {
    ptr.wrapping_byte_add(1) //~ ERROR refinement type error
}

// Adding past the top of the address space wraps around to the bottom.
#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.addr == p.addr + 16} u8
    requires p.addr > usize::MAX - 16)]
pub fn test_wraps_at_top(ptr: *const u8) -> *const u8 {
    ptr.wrapping_byte_add(16) //~ ERROR refinement type error
}
