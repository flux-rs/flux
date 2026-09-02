extern crate flux_core;

use std::ptr::NonNull;
use flux_rs::assert;

// --- dangling ---

// dereferencing a dangling pointer to a zero sized type is fine
// note that dangling pointers must be aligned
pub fn test_dangling_deref_zst() {
    let nn = NonNull::dangling();
    unsafe {
        let _val: () = nn.read();
    }
}

pub fn test_dangling_not_null() {
    let nn: NonNull<u32> = NonNull::dangling();
    let raw = nn.as_ptr();
    assert(!raw.is_null())
}
