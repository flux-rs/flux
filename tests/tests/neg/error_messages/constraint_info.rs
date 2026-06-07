// Tests for ConstraintInfo-enriched error messages.
// Each error site should produce a subdiagnostic note with either:
//   - the predicate that could not be proved (for requires-style constraints), or
//   - the expected/got types (for type-mismatch-style constraints).

#![allow(unused)]

// --- Predicate notes (from requires / constraint-type arguments) ---------------

#[flux::sig(fn(x: i32{v: v > 0 && v < 100}))] //~ NOTE this is the condition
fn needs_bounded(x: i32) {}

pub fn call_bounded_neg(n: i32) {
    needs_bounded(200); //~ ERROR refinement type
                        //~| NOTE a precondition cannot be proved
                        //~| NOTE this condition cannot be proved
}

// --- TypeMismatch notes (return value doesn't satisfy postcondition) -----------

#[flux::sig(fn(n: i32) -> i32{v: v >= 10})] //~ NOTE this is the condition
pub fn return_too_small(n: i32) -> i32 {
    n //~ ERROR refinement type
      //~| NOTE a postcondition cannot be proved
      //~| NOTE expected
}
