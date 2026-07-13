extern crate flux_core;

// missing alignment
#[flux::spec(fn (p: {*mut[@base, @addr, @size] u32 | addr > 0 && addr >= base && size >= 4}))]
pub fn test_write_bytes_unaligned(p: *mut u32) {
    unsafe { std::ptr::write_bytes(p, 0, 1) } //~ ERROR refinement type error
}

// insufficient space (only 3 bytes for a 4-byte write)
#[flux::spec(fn (p: {*mut[@base, @addr, @size] u32 | addr > 0 && addr >= base && size == 3 && addr % 4 == 0}))]
pub fn test_write_bytes_too_small(p: *mut u32) {
    unsafe { std::ptr::write_bytes(p, 0, 1) } //~ ERROR refinement type error
}

// null pointer with nonzero count
#[flux::spec(fn (p: {*mut[@base, @addr, @size] u32 | addr == 0 && addr % 4 == 0}))]
pub fn test_write_bytes_null(p: *mut u32) {
    unsafe { std::ptr::write_bytes(p, 0, 1) } //~ ERROR refinement type error
}
