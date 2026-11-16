// Test mixing `local qualifier`s, `local axiom`s and global `axiom`s in the same `defs!` block

use flux_attrs::*;

defs! {
    fn f(x: int) -> int;
    fn g(x: int) -> int;

    local qualifier Bound(x: int, y: int) { x <= y }

    local axiom FPos(x: int) { f(x) > 0 }

    axiom GPos(x: int) { g(x) > 0 }

    local axiom FMono(x: int, y: int) { x <= y => f(x) <= f(y) }
}

#[spec(fn(bool[true]))]
fn assert(_b: bool) {}

#[trusted]
#[spec(fn(x: i32) -> i32[f(x)])]
fn f(x: i32) -> i32 {
    x
}

#[trusted]
#[spec(fn(x: i32) -> i32[g(x)])]
fn g(x: i32) -> i32 {
    x
}

// global axioms are always available
pub fn test_global(x: i32) {
    assert(g(x) > 0);
}

#[axioms(FPos)]
pub fn test_one(x: i32) {
    assert(f(x) > 0);
}

#[axioms(FPos, FMono)]
#[qualifiers(Bound)]
pub fn test_two(x: i32, y: i32) {
    if x <= y {
        assert(0 < f(x) && f(x) <= f(y));
    }
}

// naming a global axiom is allowed (and has no effect)
#[axioms(GPos)]
pub fn test_named_global(x: i32) {
    assert(g(x) > 0);
}
