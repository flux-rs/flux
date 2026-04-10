extern crate flux_core;

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
