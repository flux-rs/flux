//@aux-build:flux_mod_children_aux.rs

extern crate flux_mod_children_aux;

// def in another crate used with a qualified path
#[flux::sig(fn(x: i32) -> i32[flux_mod_children_aux::mod_a::shift(x)])]
pub fn test(x: i32) -> i32 {
    x + 1
}
