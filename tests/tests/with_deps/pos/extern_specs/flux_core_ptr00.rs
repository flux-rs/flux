extern crate flux_core;

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 4 && addr % 4 == 0}) -> i32)]
fn read(ptr: *const i32) -> i32 {
    unsafe { std::ptr::read(ptr) }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 10 && addr % 4 == 0}) -> i32)]
fn read_ix(ptr: *const i32) -> i32 {
    unsafe { std::ptr::read(ptr) }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 4 && addr % 4 == 0}, value: i32))]
fn write_i32(ptr: *mut i32, value: i32) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 99 && addr % 4 == 0}, value: i32))]
fn write_ix_i32(ptr: *mut i32, value: i32) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] T | addr >= base && addr > 0 && size >= T::size_of() && addr % T::align_of() == 0}, value: T)
    requires T::size_of() > 0)]
fn write<T>(ptr: *mut T, value: T) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] T | addr >= base && addr > 0 && size == 99 && addr % T::align_of() == 0}, value: T)
    requires T::size_of() > 0 && T::size_of() <= 99)]
fn write_ix<T>(ptr: *mut T, value: T) {
    unsafe {
        std::ptr::write(ptr, value);
    }
}

// --- method forms ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 4 && addr % 4 == 0}) -> i32)]
fn read_method(ptr: *const i32) -> i32 {
    unsafe { ptr.read() }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 4 && addr % 4 == 0}, value: i32))]
fn write_method(ptr: *mut i32, value: i32) {
    unsafe { ptr.write(value) }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 4 && addr % 4 == 0}, value: i32) -> i32)]
fn replace_method(ptr: *mut i32, value: i32) -> i32 {
    unsafe { ptr.replace(value) }
}
