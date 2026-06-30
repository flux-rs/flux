extern crate flux_core;

use std::ptr::NonNull;

// --- add ---

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && size > 8 && addr != 0 && addr % 4 == 0)]
pub fn test_add_ex(nn: NonNull<i32>) {
    unsafe {
        let _val0 = std::ptr::read(nn.add(0).as_ptr());
        let _val1 = std::ptr::read(nn.add(1).as_ptr());
        let _val2 = std::ptr::read(nn.add(2).as_ptr()); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && size == 8 && addr != 0 && addr % 4 == 0)]
pub fn test_add_ix(nn: NonNull<i32>) {
    unsafe {
        let _val0 = std::ptr::read(nn.add(0).as_ptr());
        let _val1 = std::ptr::read(nn.add(1).as_ptr());
        let _val2 = std::ptr::read(nn.add(2).as_ptr()); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && size > 8 && addr != 0 && addr % 4 == 0)]
pub fn test_add_mut_ex(nn: NonNull<i32>) {
    unsafe {
        std::ptr::write(nn.add(0).as_ptr(), 10);
        std::ptr::write(nn.add(1).as_ptr(), 20);
        std::ptr::write(nn.add(2).as_ptr(), 30); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && size == 8 && addr != 0 && addr % 4 == 0)]
pub fn test_add_mut_ix(nn: NonNull<i32>) {
    unsafe {
        std::ptr::write(nn.add(0).as_ptr(), 10);
        std::ptr::write(nn.add(1).as_ptr(), 20);
        std::ptr::write(nn.add(2).as_ptr(), 30); //~ ERROR refinement type error
    }
}

// --- offset (signed count) ---

// forward offset past end: size == 4 holds only one i32; offset(2) needs 8 bytes
#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size == 4 && addr % 4 == 0)]
pub fn test_offset_forward_too_far(nn: NonNull<i32>) {
    unsafe {
        let _ = nn.offset(2); //~ ERROR refinement type error
    }
}

// backward offset before base: addr == base means no room behind the pointer
#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr == base && size >= 4 && addr % 4 == 0)]
pub fn test_offset_backward_past_base(nn: NonNull<i32>) {
    unsafe {
        let _ = nn.offset(-1); //~ ERROR refinement type error
                               //~| ERROR refinement type error
    }
}

// --- sub ---

// sub(1) moves addr before base; ptr is at the start of its allocation
pub fn test_sub_oob(buf: &mut [i32; 2]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        std::ptr::write(nn.sub(1).as_ptr(), 10); //~ ERROR refinement type error
                                                  //~| ERROR refinement type error
                                                  //~| ERROR refinement type error
    }
}
