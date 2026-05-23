extern crate flux_core;

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
