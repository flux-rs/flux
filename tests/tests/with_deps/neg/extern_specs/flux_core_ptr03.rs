extern crate flux_core;

// --- sub ---

// sub(1) moves addr before base, making the pointer invalid for reads/writes
pub fn test_sub_oob(buf: &mut [i32; 2]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        std::ptr::write(ptr.sub(1), 10); //~ ERROR refinement type error
    }
}

// --- byte_add ---

// byte_add(8) exhausts the 8-byte buffer, leaving size == 0
pub fn test_byte_add_oob(buf: &mut [i32; 2]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        std::ptr::write(ptr.byte_add(8), 10); //~ ERROR refinement type error
    }
}

// --- byte_sub ---

// byte_sub(8) moves addr before base
pub fn test_byte_sub_oob(buf: &mut [i32; 2]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        let ptr1 = ptr.byte_add(4);
        std::ptr::write(ptr1.byte_sub(8), 10); //~ ERROR refinement type error
    }
}
