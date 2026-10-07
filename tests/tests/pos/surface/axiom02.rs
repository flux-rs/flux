// Axioms about operations that are made uninterpreted with `uif_ops`

use flux_attrs::*;

defs! {
    axiom MulComm(x: int, y: int) { x * y == y * x }


    // A positive multiple of `c` is at least `c`. Pattern: `x % c`.
    axiom ModPosGe(x: int, c: int) {
        (c > 0 && x > 0 && [%](x, c) == 0) => x >= c
    }
}

// With `uif_ops = "*"`, `x * y` is an uninterpreted function, so commutativity needs the axiom
// (which is instantiated using the terms `x * y` and `y * x` as its pattern)
#[opts(uif_ops = "*")]
#[spec(fn(x: i32, y: i32) -> i32{v: v == y * x})]
pub fn mul_comm(x: i32, y: i32) -> i32 {
    x * y
}

// Without `uif_ops`, `*` is interpreted, so the axiom is emitted without a pattern
#[spec(fn(x: i32) -> i32{v: v == x * 2})]
pub fn mul_two(x: i32) -> i32 {
    x + x
}

#[opts(uif_ops = "%")]
#[spec(fn(x: i32, c: i32) -> bool[true])]
pub fn mod_pos_ge(x: i32, c: i32) -> bool {
    if c > 0 && x > 0 && x % c == 0 { x >= c } else { true }
}
