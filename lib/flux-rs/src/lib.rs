#![no_std]

pub mod bitvec;

pub use attrs::*;
pub use flux_attrs as attrs;

#[sig(fn(bool[true]) )]
pub fn assert(_: bool) {}

#[sig (fn() -> _ requires false)]
pub fn impossible() -> ! {
    panic!("impossible case")
}
