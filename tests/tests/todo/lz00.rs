use std::mem;

struct Shared {
    vec: Vec<i32>,
}

pub struct BytesMut {
    data: *mut Shared,
}

fn test(bytes: BytesMut) {
    let shared = bytes.data as *mut Shared;
    let vec = mem::replace(unsafe { &mut (*shared).vec }, Vec::new());
}
