//@aux-build:extern_spec_late_bound_lifetime_aux.rs

#![deny(late_bound_lifetime_arguments)]

extern crate extern_spec_late_bound_lifetime_aux;

use extern_spec_late_bound_lifetime_aux::{f1, f2, zero};
use flux_attrs::extern_spec;

#[extern_spec]
#[flux::spec(fn(&i32) -> &i32[0])]
fn zero<'a>(x: &i32) -> &'a i32;

#[flux::spec(fn(&i32) -> i32[0])]
pub fn test(x: &i32) -> i32 {
    *zero(x)
}

#[extern_spec]
#[flux::spec(fn(&u8) -> &u8[42])]
fn f1<'b>(arg: &u8) -> &'b u8;

#[extern_spec]
#[flux::spec(fn(&u8) -> &u8[42])]
fn f2<'a, 'b>(arg: &'a u8) -> &'b u8;

#[flux::spec(fn(&u8) -> u8[42])]
pub fn test_f1(x: &u8) -> u8 {
    *f1(x)
}

#[flux::spec(fn(&u8) -> u8[42])]
pub fn test_f2(x: &u8) -> u8 {
    *f2(x)
}
