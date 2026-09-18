extern crate flux_core;

use std::ptr::NonNull;

// --- cast ---

#[flux::spec(fn(nn: NonNull<u8>[@base, @addr, @size])
    requires addr >= base && addr > 0 && size == 1 && addr % 8 == 0)]
pub fn test_cast_does_not_create_extent(nn: NonNull<u8>) {
    let wide = nn.cast::<u64>();
    unsafe {
        wide.write(0); //~ ERROR refinement type error
    }
}

#[flux::spec(fn(nn: NonNull<u8>[@base, @addr, @size])
    requires addr >= base && addr > 0 && size >= 8 && addr % 8 != 0)]
pub fn test_cast_does_not_create_alignment(nn: NonNull<u8>) {
    let wide = nn.cast::<u64>();
    unsafe {
        wide.write(0); //~ ERROR refinement type error
    }
}
