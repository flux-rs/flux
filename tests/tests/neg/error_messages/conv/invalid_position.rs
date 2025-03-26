use flux_rs::attrs::*;

defs! {
    fn add1(x: int) -> int {
        x + 1
    }
}

#[opaque]
#[refined_by(p: int -> int)]
struct S;

#[sig(fn(S[add1]))] //~ ERROR expression not allowed in this position
fn test(x: S) {}
