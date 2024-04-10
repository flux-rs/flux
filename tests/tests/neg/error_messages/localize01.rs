#![allow(unused)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn() -> RVec<i32>[1])]
fn make_singleton0() -> RVec<i32> {
    RVec::new() //~ ERROR refinement type
}

#[flux::sig(fn() -> RVec<i32{v: v > 0}>[1])]
fn make_singleton1() -> RVec<i32> {
    let mut v = RVec::new();
    v.push(0);
    v //~ ERROR refinement type
}
