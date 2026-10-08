//@aux-build:define_fun_aux.rs

// Tests that `define-fun`s for spec functions coming from different crates are emitted in
// dependency order. `inc3`, `inc2`, and `inc` are all encoded as `define-fun`. Since `inc3`
// calls `inc2`, which calls `inc`, the definitions of `inc` and `inc2` must come before the one for
// `inc3`, otherwise the SMT solver fails with an unknown constant.

extern crate define_fun_aux;

use flux_attrs::*;

defs! {
    fn inc3(x: int) -> int { define_fun_aux::inc2(x) + 1 }
}

#[spec(fn(x: i32{x < 100}) -> i32[inc3(x)])]
pub fn test00(x: i32) -> i32 {
    x + 3
}

#[spec(fn(x: i32{x < 100}) -> i32[define_fun_aux::inc(define_fun_aux::inc(x))])]
pub fn test01(x: i32) -> i32 {
    x + 2
}
