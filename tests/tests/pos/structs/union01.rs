//@aux-build:union01_aux.rs

// Refinements on unions must be available to downstream crates.

extern crate union01_aux;

use union01_aux::{MyUnion, uninit};

#[flux::sig(fn(MyUnion[false]))]
fn take_uninit(_: MyUnion) {}

pub fn test() {
    take_uninit(uninit());
}
