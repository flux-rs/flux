// ignore-test ignore until we implement resolving of record sorts

#[flux::refined_by(f: int)]
pub struct S {
    #[flux::field(i32[@f])]
    f: i32,
}

#[flux::alias(type A(n: S) = i32{v: v < n.f })]
type A = i32;

#[flux::sig(fn(s: S, x: A(s)))]
pub fn test0(s: S, x: A) {}

pub fn test1() {
    let s = S { f: 10 };
    test0(s, 4);
}
