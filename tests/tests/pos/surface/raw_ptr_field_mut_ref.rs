#![flux::opts(allow_raw_deref = "ok")]

// Test that we can take a mutable reference to a field accessed through a dereferenced raw pointer

struct Shared {
    vec: Vec<i32>,
}

pub struct BytesMut {
    data: *mut Shared,
}

fn test(bytes: BytesMut) {
    let shared = bytes.data as *mut Shared;
    unsafe {
        let _ = &mut (*shared).vec;
    }
}
