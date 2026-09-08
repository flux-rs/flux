#![feature(allocator_api)]

extern crate flux_core;

use core::{
    alloc::{Allocator, Layout},
    ptr::NonNull,
};

// A block as `allocate`/`grow`/`shrink` return it: at the start of its own allocation,
// tracked as exactly `size` bytes long, and aligned to `align`.
#[flux::spec(fn(NonNull<[u8]>[@base, @addr, @size], usize[@lsize], usize[@lalign])
    requires base == addr && lsize == size && addr % lalign == 0)]
fn check_block(_block: NonNull<[u8]>, _size: usize, _align: usize) {}

// --- allocate ---

pub fn test_allocate<A: Allocator>(a: &A) {
    let layout = Layout::from_size_align(16, 8).unwrap();
    if let Ok(block) = a.allocate(layout) {
        check_block(block, 16, 8);
    }
}

pub fn test_allocate_of<A: Allocator>(a: &A) {
    let layout = Layout::new::<u64>();
    if let Ok(block) = a.allocate(layout) {
        check_block(block, size_of::<u64>(), align_of::<u64>());
    }
}

// A zero-sized layout still yields a block at the start of an allocation.
pub fn test_allocate_zero_sized<A: Allocator>(a: &A) {
    let layout = Layout::from_size_align(0, 1).unwrap();
    if let Ok(block) = a.allocate(layout) {
        check_block(block, 0, 1);
    }
}

pub fn test_allocate_zeroed<A: Allocator>(a: &A) {
    let layout = Layout::from_size_align(16, 8).unwrap();
    if let Ok(block) = a.allocate_zeroed(layout) {
        check_block(block, 16, 8);
    }
}

// --- deallocate ---

#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], layout: Layout[@lsize, @lalign])
    requires base == addr && lsize == size && addr % lalign == 0)]
pub unsafe fn test_deallocate<A: Allocator>(a: &A, ptr: NonNull<u8>, layout: Layout) {
    a.deallocate(ptr, layout);
}

// KNOWN APPROXIMATION, not a guarantee: this is UB if the block was allocated with align 16,
// and Flux accepts it anyway, since `layout_fits` can only check the address against
// `layout.align()` — see the note on alignment in `flux_core::alloc::allocator`.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], layout: Layout[@lsize, @lalign])
    requires base == addr && lsize == size && addr % 16 == 0 && lalign == 8)]
pub unsafe fn test_deallocate_aligned<A: Allocator>(a: &A, ptr: NonNull<u8>, layout: Layout) {
    a.deallocate(ptr, layout);
}

// --- grow ---

#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize <= 32)]
pub unsafe fn test_grow<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(32, 8).unwrap();
    if let Ok(block) = a.grow(ptr, old, new) {
        check_block(block, 32, 8);
    }
}

// `new_layout.size() >= old_layout.size()` permits equality, and `new_layout.align()`
// need not match `old_layout.align()`.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize == 16)]
pub unsafe fn test_grow_same_size_new_align<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(16, 32).unwrap();
    if let Ok(block) = a.grow(ptr, old, new) {
        check_block(block, 16, 32);
    }
}

#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize <= 32)]
pub unsafe fn test_grow_zeroed<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(32, 8).unwrap();
    if let Ok(block) = a.grow_zeroed(ptr, old, new) {
        check_block(block, 32, 8);
    }
}

// --- shrink ---

#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize >= 8)]
pub unsafe fn test_shrink<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(8, 8).unwrap();
    if let Ok(block) = a.shrink(ptr, old, new) {
        check_block(block, 8, 8);
    }
}

#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize >= 16)]
pub unsafe fn test_shrink_new_align<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(16, 32).unwrap();
    if let Ok(block) = a.shrink(ptr, old, new) {
        check_block(block, 16, 32);
    }
}

// --- round trip ---

// `allocate` returns a `NonNull<[u8]>` and `deallocate` takes a `NonNull<u8>`; `cast`
// carries the indices across, so the allocating layout still fits.
pub fn test_allocate_then_deallocate<A: Allocator>(a: &A) {
    let layout = Layout::from_size_align(16, 8).unwrap();
    if let Ok(block) = a.allocate(layout) {
        let ptr = block.cast::<u8>();
        unsafe { a.deallocate(ptr, layout) };
    }
}

// The same round trip through `grow`, which both consumes and produces a block.
pub fn test_allocate_then_grow_then_deallocate<A: Allocator>(a: &A) {
    let old = Layout::from_size_align(16, 8).unwrap();
    let new = Layout::from_size_align(32, 8).unwrap();
    if let Ok(block) = a.allocate(old) {
        if let Ok(grown) = unsafe { a.grow(block.cast::<u8>(), old, new) } {
            unsafe { a.deallocate(grown.cast::<u8>(), new) };
        }
    }
}
