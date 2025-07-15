// Check that associated refinements in invariants are unfolded

use flux_rs::attrs::*;

#[assoc(fn p(x: T) -> bool)]
trait Prop<T> {}

struct Gt0;

#[assoc(fn p(x: int) -> bool { x > 0 })]
impl Prop<i32> for Gt0 {}

#[refined_by(x: int)]
#[invariant(<P as Prop<i32>>::p(x))]
struct S<P: Prop<i32>> {
    #[field(i32[x])]
    x: i32,
    p: P,
}

fn assume_invariant(s: S<Gt0>) {
    flux_rs::assert(s.x > 0);
}

fn check_invariant() -> S<Gt0> {
    S { x: 1, p: Gt0 }
}
