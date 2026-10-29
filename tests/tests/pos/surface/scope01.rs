// Tests that params declared by quantifiers, `let` declarations and `requires` clauses are only
// in scope inside the construct that declares them, so the same name can be reused.

#[flux::sig(fn(x: i32) requires (forall i in 0..4 { i < x }) && (forall i in 0..4 { i >= 0 }))]
pub fn quant_reuse(_x: i32) {}

#[flux::sig(
    fn(x: i32)
    requires (forall i in 0..4 { let a = i; a < x }) && (forall j in 0..4 { let a = j; a >= 0 })
)]
pub fn let_reuse(_x: i32) {}

#[flux::sig(fn(x: i32) requires (forall i in 0..4 { let a = i; let b = a + 1; b <= x + 1 }))]
pub fn let_sequential(_x: i32) {}

#[flux::sig(fn(i: i32) requires forall i. i >= 0 => i + 1 > 0)]
pub fn requires_shadows_input(_i: i32) {}
