#[flux::opaque]
#[flux::refined_by(x: int)]
pub struct S {
    x: i32,
}

const SOME_S: S = S { x: 42 };

#[flux::sig(fn() -> S[SOME_S])] //~ ERROR constant annotation required
pub fn foo() -> S {
    SOME_S
}
