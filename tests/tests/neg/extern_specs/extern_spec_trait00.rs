//@aux-build:extern_spec_trait00_aux.rs

extern crate extern_spec_trait00_aux;

use extern_spec_trait00_aux::MyTrait;
use flux_rs::extern_spec;

#[extern_spec]
#[flux::generics(Self as base)]
#[flux::assoc(fn f(self: Self) -> bool)]
trait MyTrait {}

#[flux::trusted]
#[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})]
pub fn lib<T: MyTrait>(x: &T) -> T {
    x.method()
}

#[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})]
pub fn cli<T: MyTrait>(x: &T) -> T {
    lib(x)
}

#[flux::sig(fn<T as base>(&T) -> T{v: <T as MyTrait>::f(v)})]
pub fn cli2<T: MyTrait>(x: &T) -> T {
    lib(x) //~ ERROR refinement type error
}
