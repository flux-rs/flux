#![feature(rustc_private, try_trait_v2, try_blocks, never_type)]

extern crate rustc_errors;
extern crate rustc_index;

pub mod errors;
pub mod format;
pub mod index;
pub mod iter;

pub trait SemiGroup {
    fn append(self, b: Self) -> Self;
}
