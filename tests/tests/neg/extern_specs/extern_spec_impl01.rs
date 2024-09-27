//@aux-build:extern_spec_impl01_aux.rs

extern crate extern_spec_impl01_aux;

use extern_spec_impl01_aux::{MyTrait, OtherTrait};
use flux_rs::extern_spec;

#[extern_spec]
impl<T> MyTrait for Vec<T> {
    #[flux::sig(fn() -> i32[10])]
    fn foo() -> i32;
}

#[flux::sig(fn () -> i32[0])]
pub fn test_bad1() -> i32 {
    <Vec<i32> as MyTrait>::foo() //~ ERROR refinement type
}

#[flux::sig(fn () -> i32[0])]
pub fn test_bad2() -> i32 {
    <Vec<i32> as OtherTrait>::foo() //~ ERROR refinement type
}

#[flux::sig(fn () -> i32[10])]
pub fn test_ok() -> i32 {
    <Vec<i32> as MyTrait>::foo()
}
