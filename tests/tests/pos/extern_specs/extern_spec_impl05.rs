//@aux-build:extern_spec_impl05_aux.rs

// An anonymous lifetime in the header of the external impl matches a named lifetime in the
// extern spec.

extern crate extern_spec_impl05_aux;

use extern_spec_impl05_aux::Wrapper;
use flux_attrs::*;

#[extern_spec(extern_spec_impl05_aux)]
#[refined_by(n: int)]
struct Wrapper;

#[extern_spec(extern_spec_impl05_aux)]
impl<'a> From<&'a i32> for Wrapper {
    #[spec(fn(&i32[@n]) -> Wrapper[n])]
    fn from(x: &'a i32) -> Wrapper;
}

#[spec(fn() -> Wrapper[1])]
pub fn test() -> Wrapper {
    Wrapper::from(&1)
}
