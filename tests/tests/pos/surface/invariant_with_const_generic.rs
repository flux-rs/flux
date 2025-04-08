// Test that const generics in invariants are properly instantiated

use flux_rs::attrs::*;

#[invariant(N > 0)]
struct S<const N: usize> {}

#[sig(fn(_) -> usize{v : v > 0})]
fn foo<const M: usize>(x: S<M>) -> usize {
    M
}
