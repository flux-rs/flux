extern crate flux_core;

use std::ptr::NonNull;

// Zero-offset arithmetic is always allowed, even for a dangling pointer.
pub fn test_nonnull_zero_offset() {
    let p = NonNull::<u64>::dangling();
    let _a = unsafe { p.add(0) };
    let _b = unsafe { p.sub(0) };
    let _c = unsafe { p.offset(0) };
    let _d = unsafe { p.byte_add(0) };
    let _e = unsafe { p.byte_sub(0) };
    let _f = unsafe { p.byte_offset(0) };
}

pub fn test_raw_zero_offset(p: *const u64) {
    let _a = unsafe { p.add(0) };
    let _b = unsafe { p.sub(0) };
    let _c = unsafe { p.offset(0) };
    let _d = unsafe { p.byte_add(0) };
    let _e = unsafe { p.byte_sub(0) };
    let _f = unsafe { p.byte_offset(0) };
}
