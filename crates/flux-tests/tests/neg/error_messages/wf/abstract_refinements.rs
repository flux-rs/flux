#[flux::sig(
    fn<refine p: int -> bool>(x: i32) -> i32{v: p(v)}
    requires x > 0 || p(x) //~ ERROR illegal use of refinement parameter
)]
fn test00(x: i32) -> i32 {
    0
}

#[flux::sig(
    fn<refine p: int -> bool>(x: i32) -> i32{v: p(v)}
    requires p == p //~ ERROR values of sort `int -> bool` cannot be compared for equality
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

#[flux::sig(fn<refine p: int -> bool>() -> S[|x| p(x) || x == 0])] //~ ERROR illegal use of refinement parameter
fn test05() -> S {
    todo!()
}

// It should be possible to accept `p` in `bool[p(0)]` but it requires some refactoring.
// In the meantime we explicitly test against it.
#[flux::sig(fn<refine p: int -> bool>() -> bool[p(0)])] //~ ERROR illegal use of refinement parameter
fn test06() -> bool {
    todo!()
}

#[flux::sig(fn(S[|x, y| true]))] //~ ERROR parameter count mismatch
fn test07(x: S) {}
