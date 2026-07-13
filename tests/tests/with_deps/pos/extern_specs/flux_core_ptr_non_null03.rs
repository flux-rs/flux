extern crate flux_core;

use std::ptr::NonNull;

// --- read ---

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) -> i32 requires addr >= base && addr > 0 && size >= 4 && addr % 4 == 0)]
pub fn test_read(nn: NonNull<i32>) -> i32 {
    unsafe { nn.read() }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) -> i32 requires addr >= base && addr > 0 && size == 10 && addr % 4 == 0)]
pub fn test_read_ix(nn: NonNull<i32>) -> i32 {
    unsafe { nn.read() }
}

// --- write ---

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size], val: i32) requires addr >= base && addr > 0 && size >= 4 && addr % 4 == 0)]
pub fn test_write(nn: NonNull<i32>, val: i32) {
    unsafe { nn.write(val) }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size], val: i32) requires addr >= base && addr > 0 && size == 99 && addr % 4 == 0)]
pub fn test_write_ix(nn: NonNull<i32>, val: i32) {
    unsafe { nn.write(val) }
}

#[flux::spec(fn<T> (nn: NonNull<T>[@base, @addr, @size], val: T) requires addr >= base && addr > 0 && size >= T::size_of() && addr % T::align_of() == 0 && T::size_of() > 0)]
pub fn test_write_generic<T>(nn: NonNull<T>, val: T) {
    unsafe { nn.write(val) }
}

