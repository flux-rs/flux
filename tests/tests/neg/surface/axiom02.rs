// Axioms about operations that are made uninterpreted with `uif_ops`

use flux_attrs::*;

defs! {
    axiom MulZero(x: int) { x * 0 == 0 }
}

// With `uif_ops = "*"`, `x * y` is an uninterpreted function, and the axiom says nothing about
// commutativity
#[opts(uif_ops = "*")]
#[spec(fn(x: i32, y: i32) -> i32{v: v == y * x})]
pub fn mul_comm(x: i32, y: i32) -> i32 {
    x * y //~ ERROR refinement type
}
