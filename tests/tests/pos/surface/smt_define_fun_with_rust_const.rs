// compile-flags: -Fsmt-define-fun

// Regression test for https://github.com/flux-rs/flux/issues/1662
// When -Fsmt-define-fun is used, Rust constants (like u32::MAX) referenced inside
// flux defs must be declared in the SMT constraint, not silently dropped.

use flux_attrs::*;

defs! {
    fn is_small(v: int) -> bool {
        v < u32::MAX
    }
}

// With the explicit bound v < 100, the solver can prove v < u32::MAX = 4_294_967_295.
#[spec(fn(v: i32{v < 100}) -> bool[is_small(v)])]
fn test(v: i32) -> bool {
    true
}
