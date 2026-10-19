//@aux-build:extern_spec_impl04_aux.rs

// An anonymous lifetime in the self type of the external impl matches a named lifetime in the
// extern spec.

extern crate extern_spec_impl04_aux;

use extern_spec_impl04_aux::{Get, Wrapper};
use flux_attrs::*;

#[extern_spec(extern_spec_impl04_aux)]
impl<'a> Get for &'a Wrapper {
    #[spec(fn(Self) -> i32{v: v > 0})]
    fn get(self) -> i32;
}

#[spec(fn(&Wrapper) -> i32{v: v > 1})]
pub fn test(w: &Wrapper) -> i32 {
    w.get() //~ ERROR refinement type
}
