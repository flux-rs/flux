extern crate flux_core;

use core::mem::MaybeUninit;

struct S {
    x: i32,
    y: i32,
}

#[repr(align(8))]
struct A(bool);

fn test_size_of() {
    flux_rs::assert(size_of::<i32>() == 4);
    flux_rs::assert(size_of::<S>() == 8);
}

fn test_align_of() {
    flux_rs::assert(align_of::<i32>() <= 8);
    flux_rs::assert(align_of::<A>() == 8);
}

fn test_write_then_assume_init() {
    let mut x = MaybeUninit::<i32>::uninit();
    x.write(42);
    let _ = unsafe { x.assume_init() };
}

fn test_write_then_assume_init_ref() {
    let mut x = MaybeUninit::<i32>::uninit();
    x.write(99);
    let _ = unsafe { x.assume_init_ref() };
}

fn test_write_overwrite_then_assume_init() {
    let mut x = MaybeUninit::<i32>::uninit();
    x.write(1);
    x.write(2);
    let _ = unsafe { x.assume_init() };
}
