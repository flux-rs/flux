//! A Rust item and a flux item of the same name in the same module are two explicit definitions,
//! so the clash is a duplicate definition, reported once where they are defined. Resolving the
//! name from outside must not report it again as an ambiguity: `resolve_ident_in_module` keeps the
//! Rust and flux children in separate pools, and the Rust one wins.
#![allow(dead_code)]

use flux_attrs::*;

mod m {
    use flux_attrs::*;

    pub struct Bag;

    defs! {
        opaque sort Bag; //~ ERROR name `Bag` is defined multiple times
    }
}

// Naming `Bag` through a qualified path resolves to the Rust item and adds no error of its own.
#[spec(fn(x: m::Bag))]
fn test(_x: m::Bag) {}
