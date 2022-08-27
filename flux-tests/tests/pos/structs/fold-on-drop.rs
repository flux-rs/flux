#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int)]
pub struct S {
    #[flux::field({i32[@a] : a >= 0})]
    f1: i32,
    _f2: Vec<i32>,
}

#[flux::sig(fn(S) -> ())]
pub fn test(mut s: S) {
    // we mutate preserving the invariant
    s.f1 += 1;
} // we check the invariant on drop
