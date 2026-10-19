#![flux::opts(allow_raw_deref = "ok")]

// Test that we can take a mutable reference to a field accessed through a dereferenced raw pointer

struct Mickey {
    vec: Vec<i32>,
}

pub struct BytesMut {
    data: *mut Mickey,
}

fn test(bytes: BytesMut) {
    let foo = bytes.data as *mut Mickey;
    unsafe {
        let _ = &mut (*foo).vec;
    }
}
