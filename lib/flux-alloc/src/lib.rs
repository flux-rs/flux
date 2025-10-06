// #![no_std]
#![cfg_attr(flux, feature(allocator_api))]

#[cfg(flux)]
pub mod slice;

#[cfg(flux)]
pub mod vec;

#[cfg(flux)]
pub mod string;

#[cfg(flux)]
pub mod rc;

// TODO(RJ): I get an "unused extern crate" warning here,
// but without it, `in_bounds` is not in scope in `lib/vec/mod.rs`.
#[cfg(flux)]
#[allow(unused_extern_crates)]
extern crate flux_core;
