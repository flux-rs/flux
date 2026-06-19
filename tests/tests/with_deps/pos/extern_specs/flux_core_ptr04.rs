extern crate flux_core;

// --- read_unaligned ---

// Only validity is required, not alignment
#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 4}) -> i32)]
pub fn test_read_unaligned(ptr: *const i32) -> i32 {
    unsafe { std::ptr::read_unaligned(ptr) }
}

// --- write_unaligned ---

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 4}, val: i32))]
pub fn test_write_unaligned(ptr: *mut i32, val: i32) {
    unsafe { std::ptr::write_unaligned(ptr, val) }
}
