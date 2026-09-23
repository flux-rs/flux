// compile-flags: -Fsuggestions-z3=process -Ffix-suggestions

#[flux::sig(fn(n: usize) requires n == 2 * (n / 2) + 1)]
fn requires_odd(n: usize) {
    let _ = n;
}

// The suggestion must preserve `2 * (n/2)`, not print `2 * n/2`.
// The latter parses as `(2 * n)/2`, making the precondition impossible.
pub fn forward(n: usize) {
    requires_odd(n); //~ ERROR refinement type error
}

#[flux::sig(fn(usize[@n]) -> () requires n == 2 * (n / 2) + 1)]
pub fn forward_with_correct_contract(n: usize) {
    requires_odd(n);
}

pub fn witness() {
    requires_odd(3);
    forward_with_correct_contract(3);
}
