#![feature(allocator_api)]

extern crate flux_core;

use core::{
    alloc::{AllocError, Allocator, Layout},
    ptr::NonNull,
};

use flux_rs::defs;

// Import the predicate rather than copying its body, which would go stale.
defs! {
    use flux_core::alloc::allocator::layout_fits;
}

// The trait's postcondition on `allocate` is an obligation on every impl, so an impl that
// says nothing is rejected — see `neg/extern_specs/flux_core_alloc02.rs`. Two ways to
// discharge it.

// 1. Prove it — restate the postcondition on the impl method. `Slab` hands out its whole
//    block and nothing smaller, so it can only serve a request for exactly `self.len`
//    bytes, which is what makes the block exactly `layout.size()` long.
#[flux::refined_by(base: int, addr: int, size: int)]
#[flux::invariant(base == addr && size >= 0)]
struct Slab {
    #[flux::field(NonNull<u8>[base, addr, size])]
    block: NonNull<u8>,
    #[flux::field(usize[size])]
    len: usize,
    #[flux::field(usize[addr])]
    addr: usize,
}

unsafe impl Allocator for Slab {
    #[flux::spec(fn(&Self, layout: Layout[@l])
        -> Result<NonNull<[u8]>{p: layout_fits(p, l)}, AllocError>)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        // Both guards are load-bearing: dropping either leaves a conjunct unprovable.
        if layout.size() != self.len {
            return Err(AllocError);
        }
        if self.addr % layout.align() != 0 {
            return Err(AllocError);
        }
        Ok(NonNull::slice_from_raw_parts(self.block, layout.size()))
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

// 2. Assume it — `#[flux::trusted_impl]` skips the impl-vs-trait check, taking the
//    implementor at their word. This is the escape hatch for an allocator that cannot state
//    its block sizes precisely enough to prove `layout_fits`. Plain `#[flux::trusted]` does
//    NOT work: the obligation is on the signature, not the body.
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
