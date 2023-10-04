#[flux::opaque]
#[flux::refined_by(p: int -> bool)]
pub struct S;

#[flux::sig(fn(x: S) -> bool[set_is_in(x.p, set_singleton(x.p))])] //~ ERROR mismatched sorts
                                                                   //~^ ERROR mismatched sorts
pub fn foo(_x: S) -> bool {
    true
}

#[flux::sig(fn(S[|x| x > 0]) -> bool[true])]
pub fn baz(x: S) -> bool {
    foo(x)
}
