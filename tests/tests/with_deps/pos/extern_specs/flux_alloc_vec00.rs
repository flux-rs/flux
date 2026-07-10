use flux_rs::{assert, attrs::*};

extern crate flux_alloc;
extern crate flux_core;

#[spec(fn(v: Vec<i32{v: v > 0}>))]
fn test(v: Vec<i32>) {
    if v.len() > 0 {
        assert(v[0] > 0);
    }
}

