// #![no_std]
#![cfg_attr(doc, deny(rustdoc::broken_intra_doc_links))]
#![cfg_attr(flux, feature(allocator_api))]
#![cfg_attr(flux, flux::no_suggestions)]

#[cfg(any(flux, doc))]
pub mod slice;

#[cfg(any(flux, doc))]
pub mod vec;

#[cfg(any(flux, doc))]
pub mod string;

#[cfg(any(flux, doc))]
pub mod rc;

// TODO(RJ): I get an "unused extern crate" warning here,
// but without it, `in_bounds` is not in scope in `lib/vec/mod.rs`.
#[cfg(any(flux, doc))]
#[allow(unused_extern_crates)]
extern crate flux_core;
