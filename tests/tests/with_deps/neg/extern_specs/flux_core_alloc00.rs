extern crate flux_core;

use core::alloc::Layout;
use flux_rs::assert;

#[repr(align(4))]
struct Foo(u8);
struct Zst;

pub fn test_layout_new() {
    let x = Layout::new::<Foo>();
    let y = Layout::new::<u16>();
    assert(x.align() != 4); //~ ERROR refinement type
    assert(x.size() != 4); //~ ERROR refinement type
    assert(y.align() == 3); //~ ERROR refinement type
    assert(y.size() == 8); //~ ERROR refinement type
}

pub unsafe fn test_from_nonpow2_align() -> Layout {
    // align must be a power of two
    Layout::from_size_align_unchecked(0, 3) //~ ERROR refinement type
}

pub unsafe fn test_from_zero_align() -> Layout {
    // align must not be zero
    Layout::from_size_align_unchecked(4, 0) //~ ERROR refinement type
}

pub unsafe fn test_from_size_overflow() -> Layout {
    // size, when rounded up to the nearest multiple of alignment, must not overflow isize.
    Layout::from_size_align_unchecked(isize::MAX as usize - 2, 4) //~ ERROR refinement type
}

pub fn test_from_valid() {
    assert(Layout::from_size_align(4, 4).is_err()); //~ ERROR refinement type
    assert(Layout::from_size_align(0, 8).is_err()); //~ ERROR refinement type
    assert(Layout::from_size_align(isize::MAX as usize - 7, 8).is_err()); //~ ERROR refinement type
}

pub fn test_from_invalid() {
    // align must be a power of two
    assert(Layout::from_size_align(0, 3).is_ok()); //~ ERROR refinement type
    // align must not be zero
    assert(Layout::from_size_align(4, 0).is_ok()); //~ ERROR refinement type
    // size, when rounded up to the nearest multiple of alignment, must not overflow isize.
    assert(Layout::from_size_align(isize::MAX as usize - 2, 3).is_ok()); //~ ERROR refinement type
}

pub fn test_array() {
    assert(Layout::array::<i32>(10).is_err()); //~ ERROR refinement type
    assert(Layout::array::<Foo>(12).is_err()); //~ ERROR refinement type
    assert(Layout::array::<u64>(usize::MAX).is_ok()); //~ ERROR refinement type
}

pub fn test_array_unwrap() {
    let x = Layout::array::<u32>(10).unwrap();
    let y = Layout::array::<Foo>(5).unwrap();
    let z = Layout::array::<Zst>(20).unwrap();
    assert(x.size() != size_of::<u32>() * 10); //~ ERROR refinement type
    assert(x.align() != align_of::<u32>()); //~ ERROR refinement type
    assert(y.size() != size_of::<Foo>() * 5); //~ ERROR refinement type
    assert(y.align() != align_of::<Foo>()); //~ ERROR refinement type
    assert(z.size() != 0); //~ ERROR refinement type
    assert(z.align() != align_of::<Zst>()); //~ ERROR refinement type
}
