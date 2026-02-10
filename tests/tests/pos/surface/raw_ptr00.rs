use flux_rs::attrs::*;

extern crate flux_core;

#[flux::spec(fn (ptr: *const {v: v > 0} i32) -> i32)]
fn read(ptr: *const i32) -> i32 {
    unsafe { std::ptr::read(ptr) }
}

#[flux::spec(fn (ptr: *const[10] i32) -> i32)]
fn read_ix(ptr: *const i32) -> i32 {
    unsafe { std::ptr::read(ptr) }
}

#[flux::spec(fn (ptr: *mut{v: v > 0} i32, value: i32))]
fn write_i32(ptr: *mut i32, value: i32) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: *mut[99] i32, value: i32))]
fn write_ix_i32(ptr: *mut i32, value: i32) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: *mut{v: v > 0} T, value: T))]
fn write<T>(ptr: *mut T, value: T) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: *mut[99] T, value: T))]
fn write_ix<T>(ptr: *mut T, value: T) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}
