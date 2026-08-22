extern crate flux_core;

use std::ptr::NonNull;

// --- cast ---

// The cast carries the indices over, so a buffer in bounds and aligned for `i64` stays
// readable through it.
pub fn test_cast_preserves_index(buf: &mut [i64; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    let bytes: NonNull<u8> = nn.cast();
    let back: NonNull<i64> = bytes.cast();
    unsafe {
        back.write(7);
        let _v = back.read();
    }
}

// Narrowing keeps the size, so arithmetic on the casted pointer stays in bounds.
pub fn test_cast_then_offset(buf: &mut [i64; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    let bytes: NonNull<u8> = nn.cast();
    unsafe {
        let _last = bytes.add(15).read();
    }
}
