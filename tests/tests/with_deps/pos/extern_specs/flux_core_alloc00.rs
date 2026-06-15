extern crate flux_core;

use flux_rs::assert;
use core::alloc::Layout;

#[repr(align(4))]
struct Foo(u8);
struct Zst;

pub fn test_layout_new() {
    let x = Layout::new::<Foo>();
    let y = Layout::new::<i64>();
    assert(x.align() == 4);
    assert(x.size() == 4);
    assert(y.align() != 3);
    assert(y.size() == 8);
}

pub unsafe fn test_unchecked_from() {
    let x = Layout::from_size_align_unchecked(size_of::<i32>(), align_of::<i32>());
    assert(x.size() == size_of::<i32>());
    assert(x.align() == align_of::<i32>());
}

pub fn test_from_valid() {
    assert(Layout::from_size_align(4, 4).is_ok());
    assert(Layout::from_size_align(0, 8).is_ok());
    assert(Layout::from_size_align(isize::MAX as usize - 7, 8).is_ok());
}

pub fn test_from_invalid() {
    // align must be a power of two
    assert(Layout::from_size_align(0, 3).is_err());
    // align must not be zero
    assert(Layout::from_size_align(4, 0).is_err());
    // size, when rounded up to the nearest multiple of alignment, must not overflow isize.
    assert(Layout::from_size_align(isize::MAX as usize - 2, 3).is_err());
}

pub fn test_from_valid_unwrap() {
    let x = Layout::from_size_align(4, 4).unwrap();
    let y = Layout::from_size_align(size_of::<Foo>(), align_of::<Foo>()).unwrap();
    assert(x.size() == 4 && x.align() == 4);
    assert(y.size() == size_of::<Foo>() && y.align() == align_of::<Foo>());
}

pub fn test_array() {
    assert(Layout::array::<i32>(10).is_ok());
    assert(Layout::array::<Foo>(12).is_ok());
    assert(Layout::array::<u64>(usize::MAX).is_err());
}

pub fn test_array_unwrap() {
    let x = Layout::array::<u32>(10).unwrap();
    let y = Layout::array::<Foo>(5).unwrap();
    let z = Layout::array::<Zst>(20).unwrap();
    assert(x.size() == size_of::<u32>() * 10);
    assert(x.align() == align_of::<u32>());
    assert(y.size() == size_of::<Foo>() * 5);
    assert(y.align() == align_of::<Foo>());
    assert(z.size() == 0);
    assert(z.align() == align_of::<Zst>());
}
