//@rustc-env:FLUX_CARGO=1
//@rustc-env:CARGO_PKG_NAME=mycrate

// Pins the re-run hint's `cargo flux check --only-check ...` command across def-path shapes
// (free fn, nested module, inherent method, trait-impl method). The hint is attached as a `note:`
// to the item's first error, and only emitted under `cargo flux` (`FLUX_CARGO=1`).
#![allow(unused)]

use flux_attrs::*;

// Free function -> `def:<name>`.
#[flux::sig(fn() -> i32{v: v > 0})] //~ NOTE this is the condition
fn foo() -> i32 {
    0 //~ ERROR refinement type
      //~| NOTE a postcondition cannot be proved
      //~| NOTE to rerun: `cargo flux check -p mycrate --only-check 'def:foo'`
}

// Nested modules -> `def:<a>::<b>::<name>`.
mod a {
    pub mod b {
        #[flux::sig(fn() -> i32{v: v > 0})] //~ NOTE this is the condition
        pub fn baz() -> i32 {
            0 //~ ERROR refinement type
              //~| NOTE a postcondition cannot be proved
              //~| NOTE to rerun: `cargo flux check -p mycrate --only-check 'def:a::b::baz'`
        }
    }
}

struct S;

// Inherent method -> `def:<Type>::<name>`.
impl S {
    #[flux::sig(fn() -> i32{v: v > 0})] //~ NOTE this is the condition
    fn inherent() -> i32 {
        0 //~ ERROR refinement type
          //~| NOTE a postcondition cannot be proved
          //~| NOTE to rerun: `cargo flux check -p mycrate --only-check 'def:S::inherent'`
    }
}

// Trait-impl method -> `def:<S as T>::f` (a def path with spaces, hence the quoting).
trait T {
    #[sig(fn() -> i32{v: v > 0})] //~ NOTE this is the condition
    fn f() -> i32;
}
impl T for S {
    fn f() -> i32 { //~ ERROR refinement type
        //~| NOTE a postcondition cannot be proved
        //~| NOTE to rerun: `cargo flux check -p mycrate --only-check 'def:<S as T>::f'`
        0
    }
}
