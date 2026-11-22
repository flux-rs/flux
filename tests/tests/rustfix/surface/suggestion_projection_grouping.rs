//@run-rustfix
//@normalize-stderr-test: "(?s).*" -> ""
//@rustfix-only-machine-applicable
//@compile-flags: -Fsuggestions=true -Ffix-suggestions

#[flux::opaque]
#[flux::refined_by(value: int)]
pub struct Value;

#[flux::sig(fn(i32{v: v > 0}))]
fn needs_positive(_n: i32) {}

// Replacing these signatures must preserve the selected expression's grouping.
#[flux::sig(fn(x: i32, y: i32, z: i32, n: i32) requires (Value { value: x + y }).value * z == 12)]
pub fn forward_product(x: i32, y: i32, z: i32, n: i32) {
    let _ = (x, y, z);
    needs_positive(n);
}

#[flux::sig(fn(x: i32, y: i32, n: i32) requires -(Value { value: x + y }).value == -3)]
pub fn forward_negation(x: i32, y: i32, n: i32) {
    let _ = (x, y);
    needs_positive(n);
}

#[flux::no_suggestions]
pub fn suggested_witness() {
    // These satisfy the original predicates but not their incorrectly grouped forms.
    forward_product(1, 3, 3, 1);
    forward_negation(1, 2, 1);
}
