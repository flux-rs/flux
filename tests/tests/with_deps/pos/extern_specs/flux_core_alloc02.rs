#![feature(allocator_api)]

extern crate flux_core;

use core::{
    alloc::{AllocError, Allocator, Layout},
    ptr::NonNull,
};

// Implementing `Allocator` under these specs. The trait's postcondition on `allocate` is
// an obligation on every impl: the impl's own signature has to entail it, so an impl that
// says nothing is rejected. There are two ways to discharge it.

// 1. Prove it — restate the trait's postcondition on the impl method. This is the honest
//    option, and the only one that actually checks the allocator against the contract.
struct Checked;

unsafe impl Allocator for Checked {
    #[flux::spec(fn(&Self, layout: Layout[@l])
        -> Result<NonNull<[u8]>{p: p.base == p.addr && l.size == p.size && p.addr % l.align == 0},
                  AllocError>)]
    fn allocate(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Err(AllocError)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

// 2. Assume it — `#[flux::trusted_impl]` skips the impl-vs-trait check for that method.
//    `Allocator` is an `unsafe trait`, so `unsafe impl` already asserts this contract;
//    this makes Flux take the implementor at their word. Note that plain
//    `#[flux::trusted]` does NOT work here: the obligation is on the signature, not the
//    body, so skipping body checking does not discharge it.
struct Trusted;

unsafe impl Allocator for Trusted {
    #[flux::trusted_impl]
    fn allocate(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Err(AllocError)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

// Preconditions do not impose the same burden: `deallocate` carries only a `requires`, and
// an impl that demands nothing is weaker than the trait, which is always sound. Neither
// impl above needed an annotation on `deallocate`.
