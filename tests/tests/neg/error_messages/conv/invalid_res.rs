use flux_rs::attrs::*;

defs! {
    fn add1(x: int) -> int {
        x + 1
    }
}

#[opaque]
#[refined_by(p: int -> int)]
struct S;

#[sig(fn(S[add1]))] //~ ERROR refinement function not allowed in this position
fn test(x: S) {}

#[spec(fn() requires S(0))] //~ ERROR struct not allowed in this position
fn foo() {}

#[spec(fn() requires S + S)] //~ ERROR struct not allowed in this position
fn baz() {}
