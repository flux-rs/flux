#![no_std]
#![cfg_attr(flux, feature(step_trait))]

mod iter;
mod ops;

#[cfg(flux)]
mod option;

#[cfg(flux)]
mod slice;
