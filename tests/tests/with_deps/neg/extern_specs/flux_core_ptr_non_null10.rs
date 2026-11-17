#![feature(extern_types)]

extern crate flux_core;

use std::ptr::NonNull;

// The slice (`4 * meta` bytes) doesn't fit in the allocation.
#[flux::spec(fn (nn: NonNull<[u32]>[@base, @addr, @size, @meta]) -> &[u32]
    requires addr >= base && size >= 4 * meta - 1 && addr % 4 == 0)]
pub fn test_slice_too_long(nn: NonNull<[u32]>) -> &'static [u32] {
    unsafe { nn.as_ref() } //~ ERROR refinement type
}

// Misaligned slice pointer.
#[flux::spec(fn (nn: NonNull<[u32]>[@base, @addr, @size, @meta]) -> &[u32]
    requires addr >= base && size >= 4 * meta)]
pub fn test_slice_misaligned(nn: NonNull<[u32]>) -> &'static [u32] {
    unsafe { nn.as_ref() } //~ ERROR refinement type
}

// Nothing is known about the size of a generic unsized pointee.
#[flux::spec(fn (nn: NonNull<T>[@base, @addr, @size, @_meta]) -> &T
    requires addr >= base && size >= 1000)]
pub fn test_unsized_generic<T: ?Sized>(nn: NonNull<T>) -> &'static T {
    // Both the size and the alignment conditions fail.
    unsafe {
        nn.as_ref() //~ ERROR refinement type
                    //~| ERROR refinement type
    }
}

unsafe extern "C" {
    pub type Opaque;
}

// Extern types are not `MetaSized`, so their size and alignment are opaque.
#[flux::spec(fn (nn: NonNull<Opaque>[@base, @addr, @size, @_meta]) -> &Opaque
    requires addr >= base && size >= 1000)]
pub fn test_extern_type(nn: NonNull<Opaque>) -> &'static Opaque {
    unsafe {
        nn.as_ref() //~ ERROR refinement type
                    //~| ERROR refinement type
    }
}
