extern crate flux_core;

// A ptr-to-ptr cast carries the `base`/`addr`/`size` index over to the casted
// pointer, but it does not conjure up bytes or alignment: `valid` and `aligned_to`
// are re-checked against the *new* pointee.

// Only 4 bytes are known to be accessible, so an 8-byte read is out of bounds even
// though the address is suitably aligned.
#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 4 && addr % 8 == 0}))]
pub fn test_cast_widen_read(ptr: *const i32) {
    let wide_ptr = ptr as *const i64;
    unsafe {
        let _v = std::ptr::read(wide_ptr); //~ ERROR refinement type error
    }
}

// A byte pointer is only known to be 1-byte aligned, so reading it as an `i32`
// cannot establish `addr % 4 == 0`.
#[flux::spec(fn (ptr: {*const[@base, @addr, @size] u8 | addr >= base && addr > 0 && size >= 4}))]
pub fn test_cast_align(ptr: *const u8) {
    let int_ptr = ptr as *const i32;
    unsafe {
        let _v = std::ptr::read(int_ptr); //~ ERROR refinement type error
    }
}

// Stepping one byte into an aligned `i32` and casting back breaks the alignment.
#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 8 && addr % 4 == 0}))]
pub fn test_cast_round_trip_unaligned(ptr: *mut i32) {
    let byte_ptr = ptr as *mut u8;
    unsafe {
        let int_ptr = byte_ptr.byte_add(1) as *mut i32;
        std::ptr::write(int_ptr, 10); //~ ERROR refinement type error
    }
}

// The preserved `size` shrinks as the byte pointer advances, so writing past the
// end of the original `i32` is caught.
#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 4 && addr % 4 == 0}))]
pub fn test_cast_byte_add_out_of_bounds(ptr: *mut i32) {
    let byte_ptr = ptr as *mut u8;
    unsafe {
        std::ptr::write(byte_ptr.byte_add(4), 255); //~ ERROR refinement type error
    }
}
