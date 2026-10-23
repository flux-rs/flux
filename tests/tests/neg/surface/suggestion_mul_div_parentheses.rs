// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: requires n == 2 * (n/2) + 1

#[flux::sig(fn(n: usize) requires n == 2 * (n / 2) + 1)]
fn requires_odd(n: usize) {
    let _ = n;
}

// The suggestion must preserve `2 * (n/2)`, not print `2 * n/2`.
// The latter parses as `(2 * n)/2`, making the precondition impossible.
#[flux::sig(fn(usize))]
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

// Compiled only after applying the suggestion: its precondition must be satisfiable.
#[cfg(flux_test_suggestions_applied)]
pub fn suggested_witness() {
    forward(3);
}
