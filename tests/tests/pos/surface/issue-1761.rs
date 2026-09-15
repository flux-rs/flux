extern crate flux_core;

pub fn test_slice_cast_is_null() {
    let slice: &[u32] = &[1, 2, 3];
    let raw_slice: *const [u32] = slice as *const [u32];
    flux_rs::assert(!raw_slice.is_null());
}

pub fn test_slice_cast_ne() {
    let slice: &[u32] = &[1, 2, 3];
    let raw_slice: *const [u32] = slice as *const [u32];
    let raw_slice_zst: *const () = raw_slice as *const ();
    flux_rs::assert(raw_slice_zst != std::ptr::null());
}
