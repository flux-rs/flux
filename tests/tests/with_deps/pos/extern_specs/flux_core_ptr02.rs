extern crate flux_core;

pub fn test(buf: &mut [u32; 2]) {
    // let mut buf: [u32; 2] = [67; 2]; // sigh, see https://github.com/flux-rs/flux/issues/1465

    let ptr: *mut u32 = buf.as_mut_ptr();

    unsafe {
        std::ptr::write(ptr.add(0), 10);
        std::ptr::write(ptr.add(1), 20);
    }
}
