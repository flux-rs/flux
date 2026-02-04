pub fn test() {
    let mut buf: [u32; 2] = [0; 2];

    let ptr: *mut u32 = buf.as_mut_ptr();

    unsafe {
        *ptr.add(0) = 10;
        *ptr.add(1) = 20;
        *ptr.add(2) = 30; //~ ERROR: refinement type
    }

}
