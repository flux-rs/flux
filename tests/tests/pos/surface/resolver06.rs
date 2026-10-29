//@aux-build:flux_mod_children_aux.rs

extern crate flux_mod_children_aux;

// def in another crate used with a qualified path
#[flux::sig(fn(x: i32) -> i32[flux_mod_children_aux::mod_a::shift(x)])]
pub fn test(x: i32) -> i32 {
    x + 1
}

// def from a second `defs!` in the same module
#[flux::sig(fn(x: i32) -> i32[flux_mod_children_aux::mod_a::shift_again(x)])]
pub fn test_again(x: i32) -> i32 {
    x + 1
}

// def at the root of another crate
#[flux::sig(fn(x: i32) -> i32[flux_mod_children_aux::root_shift(x)])]
pub fn test_root(x: i32) -> i32 {
    x + 2
}

// def in a nested module of another crate
#[flux::sig(fn(x: i32) -> i32[flux_mod_children_aux::mod_a::nested::nested_shift(x)])]
pub fn test_nested(x: i32) -> i32 {
    x + 3
}
