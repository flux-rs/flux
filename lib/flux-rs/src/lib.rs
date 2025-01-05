pub mod bitvec;

pub use flux_attrs::*;

#[sig(fn(bool[true]) )]
pub fn assert(_: bool) {}
