extern crate flux_core;

use core::mem::MaybeUninit;

struct S {
    x: i32,
    y: i32,
}

#[repr(align(8))]
struct A(bool);

fn test_size_of() {
    flux_rs::assert(size_of::<i32>() == 2); //~ ERROR refinement type
    flux_rs::assert(size_of::<S>() == 4); //~ ERROR refinement type
}

fn test_align_of() {
    flux_rs::assert(align_of::<i64>() == 3); //~ ERROR refinement type
    flux_rs::assert(align_of::<A>() == 1); //~ ERROR refinement type
}

fn test_assume_init_without_write() {
    let x = MaybeUninit::<i32>::uninit();
    let _ = unsafe { x.assume_init() }; //~ ERROR refinement type error
}

fn test_assume_init_ref_without_write() {
    let x = MaybeUninit::<i32>::uninit();
    let _ = unsafe { x.assume_init_ref() }; //~ ERROR refinement type error
}
