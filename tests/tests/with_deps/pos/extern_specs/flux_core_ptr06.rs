extern crate flux_core;

// write_bytes: valid for `count * size_of::<T>()` bytes, aligned to `align_of::<T>()`

// concrete: aligned, non-null, sufficient room for 4 u32s
#[flux::spec(fn (p: {*mut[@base, @addr, @size] u32 | addr > 0 && addr >= base && size >= 16 && addr % 4 == 0}))]
pub fn test_write_bytes_concrete(p: *mut u32) {
    unsafe { std::ptr::write_bytes(p, 0xfe, 4) }
}

// zero count: alignment is still required, but validity is trivially satisfied
#[flux::spec(fn (p: {*mut[@base, @addr, @size] u32 | addr % 4 == 0}))]
pub fn test_write_bytes_zero_count(p: *mut u32) {
    unsafe { std::ptr::write_bytes(p, 0, 0) }
}

// generic T: count * T::size_of() bytes must fit in the allocation
#[flux::spec(fn (p: {*mut[@base, @addr, @size] T | addr > 0 && addr >= base && size >= T::size_of() && addr % T::align_of() == 0})
    requires T::size_of() > 0)]
pub fn test_write_bytes_one<T>(p: *mut T) {
    unsafe { std::ptr::write_bytes(p, 0, 1) }
}
