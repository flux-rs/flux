// Test that `local axiom`s are only used by the functions that name them

use flux_attrs::*;

defs! {
    fn f(x: int) -> int;

    local axiom FPos(x: int) { f(x) > 0 }

    local axiom FMono(x: int, y: int) { x <= y => f(x) <= f(y) }
}

#[spec(fn(bool[true]))]
fn assert(_b: bool) {}

#[trusted]
#[spec(fn(x: i32) -> i32[f(x)])]
fn f(x: i32) -> i32 {
    x
}

pub fn test_none(x: i32) {
    assert(f(x) > 0); //~ ERROR refinement type
}

#[axioms(FMono)]
pub fn test_wrong(x: i32) {
    assert(f(x) > 0); //~ ERROR refinement type
}

#[axioms(FPos)]
pub fn test_missing(x: i32, y: i32) {
    if x <= y {
        assert(f(x) <= f(y)); //~ ERROR refinement type
    }
}
