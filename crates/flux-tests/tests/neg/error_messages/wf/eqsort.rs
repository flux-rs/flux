// #![feature(register_tool)]
// #![register_tool(flux)]

#[flux::opaque]
#[flux::refined_by(p: int -> bool)]
struct S;

#[flux::sig(fn(x: S) -> bool[set_is_in(x.p, set_singleton(x.p))])] //~ ERROR mismatched sorts
fn foo(x: S) -> bool {
    true
}

#[flux::sig(fn(S[|x| x > 0]) -> bool[true])]
fn baz(x: S) -> bool {
    foo(x)
}
