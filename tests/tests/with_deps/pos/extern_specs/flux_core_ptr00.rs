use flux_attrs::*;

extern crate flux_core;

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size > 0}) -> i32)]
fn read(ptr: *const i32) -> i32 {
    unsafe { std::ptr::read(ptr) }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 10}) -> i32)]
fn read_ix(ptr: *const i32) -> i32 {
    unsafe { std::ptr::read(ptr) }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && size > 0}, value: i32))]
fn write_i32(ptr: *mut i32, value: i32) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && size == 99}, value: i32))]
fn write_ix_i32(ptr: *mut i32, value: i32) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] T | addr >= base && size > 0}, value: T))]
fn write<T>(ptr: *mut T, value: T) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] T | addr >= base && size == 99}, value: T))]
fn write_ix<T>(ptr: *mut T, value: T) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}
