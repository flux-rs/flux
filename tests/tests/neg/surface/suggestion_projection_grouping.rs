// compile-flags: -Fsuggestions-z3=process -Ffix-suggestions

#[flux::opaque]
#[flux::refined_by(value: int)]
pub struct Value;

#[flux::sig(fn(i32{v: v > 0}))]
fn needs_positive(_n: i32) {}

// Replacing these signatures must preserve the selected expression's grouping.
#[flux::sig(fn(x: i32, y: i32, z: i32, n: i32) requires (Value { value: x + y }).value * z == 12)]
pub fn forward_product(x: i32, y: i32, z: i32, n: i32) {
    let _ = (x, y, z);
    needs_positive(n); //~ ERROR refinement type error
}

#[flux::sig(fn(x: i32, y: i32, n: i32) requires -(Value { value: x + y }).value == -3)]
pub fn forward_negation(x: i32, y: i32, n: i32) {
    let _ = (x, y);
    needs_positive(n); //~ ERROR refinement type error
}
