use flux_attrs::*;

extern crate flux_core;

pub fn test_read(x: *const i32) -> i32 {
    unsafe { std::ptr::read(x) } //~ ERROR refinement type error
                                 //~| ERROR refinement type error
}

fn test_write<T>(ptr: *mut T, value: T) {
    unsafe {
        std::ptr::write(ptr, value); //~ ERROR refinement type error
                                     //~| ERROR refinement type error
    }
}

fn test_write_i32(ptr: *mut i32, value: i32) {
    unsafe {
        std::ptr::write(ptr, value); //~ ERROR refinement type error
                                     //~| ERROR refinement type error
    }
}

// --- method forms ---

fn test_read_method(x: *const i32) -> i32 {
    unsafe { x.read() } //~ ERROR refinement type error
                        //~| ERROR refinement type error
}

fn test_write_method(ptr: *mut i32, value: i32) {
    unsafe {
        ptr.write(value); //~ ERROR refinement type error
                          //~| ERROR refinement type error
    }
}

fn test_replace_method(ptr: *mut i32, value: i32) -> i32 {
    unsafe { ptr.replace(value) } //~ ERROR refinement type error
                                  //~| ERROR refinement type error
}
