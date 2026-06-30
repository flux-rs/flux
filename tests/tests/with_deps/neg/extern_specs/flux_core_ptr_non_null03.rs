extern crate flux_core;

use std::ptr::NonNull;

// --- read ---

// unconstrained NonNull: can't prove valid or aligned
pub fn test_read(nn: NonNull<i32>) -> i32 {
    unsafe { nn.read() } //~ ERROR refinement type error
                         //~| ERROR refinement type error
}

// --- write ---

// unconstrained NonNull: can't prove valid or aligned
pub fn test_write(nn: NonNull<i32>, val: i32) {
    unsafe { nn.write(val) } //~ ERROR refinement type error
                              //~| ERROR refinement type error
}

// --- len ---

// size == 12 → len() == 3, not 4
#[flux::spec(fn (nn: NonNull<[i32]>[@base, @addr, @size]) requires size == 12)]
pub fn test_len_wrong(nn: NonNull<[i32]>) {
    use flux_rs::assert;
    assert(nn.len() == 4); //~ ERROR refinement type error
}
