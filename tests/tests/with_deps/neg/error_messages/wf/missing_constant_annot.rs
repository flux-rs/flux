#[flux_rs::opaque]
#[flux_rs::refined_by(x: int)]
pub struct S {
    x: i32,
}

const SOME_S: S = S { x: 42 };

#[flux_rs::sig(fn() -> S[SOME_S])] //~ ERROR constant annotation required
pub fn foo() -> S {
    SOME_S
}
