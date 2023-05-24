#![feature(register_tool, custom_inner_attributes)]
#![register_tool(flux)]

#[derive(Clone, Copy)]
#[flux::refined_by(p: int -> bool)]
pub struct S;

#[flux::sig(fn(x: i32) -> S[|y| y > x])]
pub fn gt(x: i32) -> S {
    S
}

#[flux::sig(fn(x: i32) -> S[|y| y < x])]
pub fn lt(x: i32) -> S {
    S
}

#[flux::sig(fn(S[@p1], S[@p2]) -> S[|x| p1(x) || p2(x)])]
pub fn or(_: S, _: S) -> S {
    S
}

#[flux::sig(fn(S[@p], x: i32{ p(x) }))]
pub fn check(_: S, x: i32) {}

pub fn test() {
    let s = or(gt(10), lt(0));
    check(s, 10); //~ ERROR refinement type
    check(s, 5); //~ ERROR refinement type
}
