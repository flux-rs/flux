//@aux-build:extern_spec_impl02_aux.rs

extern crate extern_spec_impl02_aux;

use extern_spec_impl02_aux::{bob, MyTrait};
use flux_rs::extern_spec;

#[extern_spec]
#[flux::assoc(fn f(x: int) -> bool { 10 < x } )]
impl MyTrait for usize {}

#[flux::sig(fn () -> i32{v: 100 < v})]
pub fn test_fail() -> i32 {
    let u: usize = 0;
    bob(&u) //~ ERROR refinement type
}

#[flux::sig(fn () -> i32{v: 10 < v})]
pub fn test_ok() -> i32 {
    let u: usize = 0;
    bob(&u)
}
