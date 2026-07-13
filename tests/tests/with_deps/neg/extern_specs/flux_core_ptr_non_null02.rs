extern crate flux_core;

use std::ptr::NonNull;

// --- sub ---

// base == 0, addr == 1 * size_of::<i32>() == 4: all requires of sub(1) are satisfied,
// but the result address is 0, violating the NonNull invariant addr != 0
#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires base == 0 && addr == 4 && size >= 0)]
pub fn test_sub_null_result(nn: NonNull<i32>) {
    unsafe {
        let _ = nn.sub(1); //~ ERROR refinement type error
    }
}

// --- byte_add ---

// byte_add(8) exhausts the 8-byte buffer, leaving size == 0
pub fn test_byte_add_oob(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        std::ptr::write(nn.byte_add(8).as_ptr(), 10); //~ ERROR refinement type error
    }
}

// --- byte_sub ---

// byte_sub(8) moves addr before base
pub fn test_byte_sub_oob(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn1 = nn.byte_add(4);
        std::ptr::write(nn1.byte_sub(8).as_ptr(), 10); //~ ERROR refinement type error
                                                        //~| ERROR refinement type error
                                                        //~| ERROR refinement type error
    }
}

// --- byte_offset ---

// forward too far: count(9) > size(8)
pub fn test_byte_offset_forward_oob(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let _ = nn.byte_offset(9); //~ ERROR refinement type error
    }
}

// backward before base: fresh ptr has addr == base, so addr + (-1) < base
pub fn test_byte_offset_backward_oob(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let _ = nn.byte_offset(-1); //~ ERROR refinement type error
    }
}
