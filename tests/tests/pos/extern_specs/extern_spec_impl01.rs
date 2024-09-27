//@aux-build:extern_spec_impl01_aux.rs

extern crate extern_spec_impl01_aux;

use extern_spec_impl01_aux::MyTrait;
use flux_rs::extern_spec;

#[extern_spec]
impl<T> MyTrait for Vec<T> {
    #[flux::sig(fn() -> i32[10])]
    fn foo() -> i32;
}

#[flux::sig(fn () -> i32[10])]
pub fn test_ok() -> i32 {
    <Vec<i32> as MyTrait>::foo()
}
