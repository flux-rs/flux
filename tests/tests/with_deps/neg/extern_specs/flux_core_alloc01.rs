#![feature(allocator_api)]

extern crate flux_core;

use core::{
    alloc::{Allocator, Layout},
    ptr::NonNull,
};

#[flux::spec(fn(NonNull<[u8]>[@base, @addr, @size], usize[@lsize], usize[@lalign])
    requires base == addr && lsize == size && addr % lalign == 0)]
fn check_block(_block: NonNull<[u8]>, _size: usize, _align: usize) {}

// --- allocate ---

// The block is tracked as exactly `layout.size()` bytes; the surplus an allocator may
// hand back on top of that is not modelled.
pub fn test_allocate_too_large<A: Allocator>(a: &A) {
    let layout = Layout::from_size_align(16, 8).unwrap();
    if let Ok(block) = a.allocate(layout) {
        check_block(block, 17, 8); //~ ERROR refinement type
    }
}

// The block is only guaranteed to be aligned to `layout.align()`.
pub fn test_allocate_overaligned<A: Allocator>(a: &A) {
    let layout = Layout::from_size_align(16, 8).unwrap();
    if let Ok(block) = a.allocate(layout) {
        check_block(block, 16, 16); //~ ERROR refinement type
    }
}

// `allocate_zeroed` carries the same guarantees as `allocate`, and no more.
pub fn test_allocate_zeroed_too_large<A: Allocator>(a: &A) {
    let layout = Layout::from_size_align(16, 8).unwrap();
    if let Ok(block) = a.allocate_zeroed(layout) {
        check_block(block, 17, 8); //~ ERROR refinement type
    }
}

// --- deallocate ---

// `ptr` must be aligned to `layout.align()`.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], layout: Layout[@lsize, @lalign])
    requires base == addr && lsize == size)]
pub unsafe fn test_deallocate_unaligned<A: Allocator>(a: &A, ptr: NonNull<u8>, layout: Layout) {
    a.deallocate(ptr, layout); //~ ERROR refinement type
}

// `layout` must fit the block, so it may not be larger than the block.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], layout: Layout[@lsize, @lalign])
    requires base == addr && size == lsize - 1 && addr % lalign == 0)]
pub unsafe fn test_deallocate_undersized_block<A: Allocator>(
    a: &A,
    ptr: NonNull<u8>,
    layout: Layout,
) {
    a.deallocate(ptr, layout); //~ ERROR refinement type
}

// Nor smaller: `layout.size()` is bounded below by the size the block was allocated with.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], layout: Layout[@lsize, @lalign])
    requires base == addr && size == lsize + 8 && addr % lalign == 0)]
pub unsafe fn test_deallocate_oversized_block<A: Allocator>(
    a: &A,
    ptr: NonNull<u8>,
    layout: Layout,
) {
    a.deallocate(ptr, layout); //~ ERROR refinement type
}

// `ptr` must denote the start of a currently allocated block, not an interior pointer.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], layout: Layout[@lsize, @lalign])
    requires addr > base && lsize == size && addr % lalign == 0)]
pub unsafe fn test_deallocate_interior<A: Allocator>(a: &A, ptr: NonNull<u8>, layout: Layout) {
    a.deallocate(ptr, layout); //~ ERROR refinement type
}

// --- grow ---

// `new_layout.size()` must be at least `old_layout.size()`.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize == 16)]
pub unsafe fn test_grow_smaller<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(8, 8).unwrap();
    let _ = a.grow(ptr, old, new); //~ ERROR refinement type
}

// `old_layout` must fit the block.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && size == osize - 1 && addr % oalign == 0 && osize <= 32)]
pub unsafe fn test_grow_old_layout_unfit<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(32, 8).unwrap();
    let _ = a.grow(ptr, old, new); //~ ERROR refinement type
}

// The grown block is tracked as exactly `new_layout.size()` bytes.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize <= 32)]
pub unsafe fn test_grow_too_large<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(32, 8).unwrap();
    if let Ok(block) = a.grow(ptr, old, new) {
        check_block(block, 33, 8); //~ ERROR refinement type
    }
}

// `grow_zeroed` requires `new_layout.size()` to be at least `old_layout.size()` too.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize == 16)]
pub unsafe fn test_grow_zeroed_smaller<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(8, 8).unwrap();
    let _ = a.grow_zeroed(ptr, old, new); //~ ERROR refinement type
}

// --- shrink ---

// `new_layout.size()` must be at most `old_layout.size()`.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize == 16)]
pub unsafe fn test_shrink_larger<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(32, 8).unwrap();
    let _ = a.shrink(ptr, old, new); //~ ERROR refinement type
}

// `old_layout` must fit the block, so it may not be smaller than the block either.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && size == osize + 8 && addr % oalign == 0 && osize >= 8)]
pub unsafe fn test_shrink_old_layout_undersized<A: Allocator>(
    a: &A,
    ptr: NonNull<u8>,
    old: Layout,
) {
    let new = Layout::from_size_align(8, 8).unwrap();
    let _ = a.shrink(ptr, old, new); //~ ERROR refinement type
}

// The shrunk block is only guaranteed to be aligned to `new_layout.align()`.
#[flux::spec(fn(&A, ptr: NonNull<u8>[@base, @addr, @size], old: Layout[@osize, @oalign])
    requires base == addr && osize == size && addr % oalign == 0 && osize >= 8)]
pub unsafe fn test_shrink_overaligned<A: Allocator>(a: &A, ptr: NonNull<u8>, old: Layout) {
    let new = Layout::from_size_align(8, 8).unwrap();
    if let Ok(block) = a.shrink(ptr, old, new) {
        check_block(block, 8, 16); //~ ERROR refinement type
    }
}
