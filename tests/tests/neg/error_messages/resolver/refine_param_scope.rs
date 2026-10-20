// Params declared by quantifiers, `let` declarations and `requires` clauses are not in scope
// outside the construct that declares them.

#[flux::sig(fn(x: i32) -> i32[y] requires forall y. y >= 0 => y > x)] //~ ERROR cannot find value `y` in this scope
pub fn requires_in_output(x: i32) -> i32 {
    x
}

#[flux::sig(fn(x: i32{v: v > y}) requires forall y. y >= 0)] //~ ERROR cannot find value `y` in this scope
pub fn requires_in_input(_x: i32) {}

#[flux::sig(fn(x: i32) requires (forall i in 0..4 { i < x }) && i > 0)] //~ ERROR cannot find value `i` in this scope
pub fn quant_after_body(_x: i32) {}

#[flux::sig(fn(x: i32) requires (forall i in 0..4 { let a = i; a < x }) && a > 0)] //~ ERROR cannot find value `a` in this scope
pub fn let_after_block(_x: i32) {}

#[flux::sig(fn(x: i32) requires (forall i in 0..4 { let a = a; a < x }))] //~ ERROR cannot find value `a` in this scope
pub fn let_in_own_init(_x: i32) {}
