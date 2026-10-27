// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: requires v < n.len
#[path = "../../lib/rvec.rs"]
mod rvec;

use rvec::RVec;

#[flux::sig(fn(&RVec<T>, usize) -> &T)]
fn index<T>(n: &RVec<T>, v: usize) -> &T {
    n.get(v) //~ ERROR refinement type error
}

#[cfg(flux_test_suggestions_applied)]
fn witness() {
    let values = RVec::from_array([42]);
    let _ = index(&values, 0);
}
