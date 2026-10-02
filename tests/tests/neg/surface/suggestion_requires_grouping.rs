// compile-flags: -Fsuggestions-z3=process -Ffix-suggestions

#[flux::sig(fn(i32{v: v > 0}))]
fn needs_positive(_n: i32) {}

// Replacing this signature must not join its requirements as `a || b && c`.
#[flux::sig(fn(a: bool, b: bool, c: bool, n: i32) requires a || b, c)]
pub fn forward(a: bool, b: bool, c: bool, n: i32) {
    let _ = (a, b, c);
    needs_positive(n); //~ ERROR refinement type error
}
