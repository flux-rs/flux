extern crate flux_core;

use std::ptr::NonNull;

// --- byte_add ---

pub fn test_byte_add(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        std::ptr::write(nn.byte_add(0).as_ptr(), 10);
        std::ptr::write(nn.byte_add(4).as_ptr(), 20);
    }
}

// --- byte_sub ---

pub fn test_byte_sub(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn1 = nn.byte_add(4);
        let nn0 = nn1.byte_sub(4);
        std::ptr::write(nn0.as_ptr(), 10);
        std::ptr::write(nn1.as_ptr(), 20);
    }
}

// --- byte_offset (signed count — forward and backward) ---

// forward: byte_offset(4) advances by 4 bytes to the second element
pub fn test_byte_offset_forward(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        std::ptr::write(nn.byte_offset(0).as_ptr(), 10);
        std::ptr::write(nn.byte_offset(4).as_ptr(), 20);
    }
}

// backward: advance then step back; writes both elements
pub fn test_byte_offset_backward(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn1 = nn.byte_add(4);
        let nn0 = nn1.byte_offset(-4);
        std::ptr::write(nn0.as_ptr(), 10);
        std::ptr::write(nn1.as_ptr(), 20);
    }
}
