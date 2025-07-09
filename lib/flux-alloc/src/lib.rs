// #![no_std]
#![cfg_attr(flux, feature(allocator_api))]

#[cfg(flux)]
pub mod vec;

// TODO(RJ): I get an "unused extern crate" warning here,
// but without it, `in_bounds` is not in scope in `lib/vec/mod.rs`.
#[cfg(flux)]
extern crate flux_core;
