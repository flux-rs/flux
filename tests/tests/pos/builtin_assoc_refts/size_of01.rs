// Test spec on `core::mem::size_of`

extern crate flux_core;

struct S {
    x: i32,
    y: i32,
}

fn test() {
    flux_rs::assert(size_of::<i32>() == 4);
    flux_rs::assert(size_of::<S>() == 8);
}
