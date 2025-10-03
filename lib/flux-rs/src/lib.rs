#![no_std]
extern crate alloc;

extern crate flux_alloc;
extern crate flux_core;

pub mod bitvec;

pub use attrs::*;
pub use flux_attrs as attrs;

#[sig(fn(bool[true]) )]
pub fn assert(_: bool) {}

#[sig (fn() -> _ requires false)]
pub fn impossible() -> ! {
    panic!("impossible case")
}

#[trusted]
#[spec(fn (&str[@s]) -> alloc::string::String[s])]
pub fn mk_string(s: &str) -> alloc::string::String {
    alloc::string::String::from(s)
}
