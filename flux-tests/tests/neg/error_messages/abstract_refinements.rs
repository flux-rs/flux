#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(
    fn<p: int -> bool>(x: i32) -> i32{v: p(v)}
    requires x > 0 || p(x) //~ ERROR illegal use of refinement parameter
)]
fn test00(x: i32) -> i32 {
    0
}

#[flux::sig(
    fn<p: int -> bool>(x: i32) -> i32{v: p(v)}
    requires p == p //~ ERROR illegal use of refinement parameter
    //~^ ERROR illegal use of refinement parameter
)]
fn test01(x: i32) -> i32 {
    0
}

#[flux::sig(fn(i32[|a| a > 0]))] //~ ERROR mismatched sorts
fn test02(x: i32) {}

#[flux::refined_by(p: int -> bool)]
struct S {}

#[flux::sig(fn(S[|a| a + 1]))] //~ ERROR mismatched sorts
fn test03(x: S) {}

#[flux::sig(fn(S[|a| a]))] //~ ERROR mismatched sorts
fn test04(x: S) {}

#[flux::sig(fn(S[@p]) -> S[|x| p(x) || x == 0])] //~ ERROR illegal use of refinement parameter
fn test05(x: S) -> S {
    todo!()
}

#[flux::sig(fn(S[@p]) -> bool[p(0)])] //~ ERROR illegal use of refinement parameter
fn test06(x: S) -> bool {
    todo!()
}
