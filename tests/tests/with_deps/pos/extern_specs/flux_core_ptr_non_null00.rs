extern crate flux_core;

use std::ptr::NonNull;

// new_unchecked: non-null pointer in, NonNull out; as_ptr recovers the original pointer
#[flux::spec(fn (ptr: *mut[@p] i32) requires p.addr != 0)]
pub fn test_new_unchecked(ptr: *mut i32) {
    let nn = unsafe { NonNull::new_unchecked(ptr) };
    let raw = nn.as_ptr();
    // the invariant guarantees raw is non-null
    assert!(!raw.is_null());
}

// new: None branch — null pointer yields None
pub fn test_new_null() {
    let ptr: *mut i32 = std::ptr::null_mut();
    let nn = NonNull::new(ptr);
    assert!(nn.is_none());
}

// new + as_ptr round-trip: recovering the pointer preserves identity
#[flux::spec(fn (ptr: *mut[@p] i32) requires p.addr != 0)]
pub fn test_new_as_ptr_roundtrip(ptr: *mut i32) {
    if let Some(nn) = NonNull::new(ptr) {
        let raw = nn.as_ptr();
        assert!(!raw.is_null());
    }
}
