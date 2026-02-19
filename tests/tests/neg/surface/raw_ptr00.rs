use flux_rs::attrs::*;

extern crate flux_core;

pub fn test_read(x: *const i32) -> i32 {
    unsafe { std::ptr::read(x) } //~ ERROR refinement type error
}

fn test_write<T>(ptr: *mut T, value: T) {
    unsafe {
        std::ptr::write(ptr, value); //~ ERROR refinement type error
    }
}

fn test_write_i32(ptr: *mut i32, value: i32) {
    unsafe {
        std::ptr::write(ptr, value); //~ ERROR refinement type error
    }
}
