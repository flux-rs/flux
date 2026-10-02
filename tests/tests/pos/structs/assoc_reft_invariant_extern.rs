//@aux-build:assoc_reft_invariant_aux.rs

extern crate assoc_reft_invariant_aux;

use assoc_reft_invariant_aux::Foo;

// The lower bound must come from Foo's invariant in the dependency's metadata.
#[flux::spec(fn(x: &Foo) -> usize{v: v >= 1})]
pub fn read(x: &Foo) -> usize {
    x.value
}
