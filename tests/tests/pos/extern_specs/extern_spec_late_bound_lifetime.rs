//@aux-build:extern_spec_late_bound_lifetime_aux.rs

#![deny(late_bound_lifetime_arguments)]

extern crate extern_spec_late_bound_lifetime_aux;

use extern_spec_late_bound_lifetime_aux::zero;
use flux_attrs::extern_spec;

#[extern_spec]
#[flux::spec(fn(&i32) -> &i32[0])]
fn zero<'a>(x: &i32) -> &'a i32;

#[flux::spec(fn(&i32) -> i32[0])]
pub fn test(x: &i32) -> i32 {
    *zero(x)
}
