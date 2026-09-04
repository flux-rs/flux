#![feature(allocator_api)]

extern crate flux_core;

use core::{
    alloc::{AllocError, Allocator, Layout},
    ptr::NonNull,
};

// The negative counterpart of `pos/extern_specs/flux_core_alloc02.rs`. Callers assume the
// postcondition on `allocate`, so it has to be an obligation on every impl; without these
// cases, a change that stopped checking impls against it would go unnoticed.
//
// Each impl draws one "a postcondition cannot be proved" per conjunct of `layout_fits`.

// 1. An impl that promises nothing is weaker than the trait, so it is rejected.
struct Silent;

unsafe impl Allocator for Silent {
    fn allocate(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        //~^ ERROR refinement type
        //~| ERROR refinement type
        //~| ERROR refinement type
        Err(AllocError)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

// 2. `#[flux::trusted]` skips *body* checking, but the obligation is on the signature, so
//    it does not discharge it either. `#[flux::trusted_impl]` is the escape hatch.
struct Trusted;

unsafe impl Allocator for Trusted {
    #[flux::trusted]
    fn allocate(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        //~^ ERROR refinement type
        //~| ERROR refinement type
        //~| ERROR refinement type
        Err(AllocError)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}
