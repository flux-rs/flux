// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 2
// suggestion: 0 < x
// suggestion: x < 10
#[flux::trusted]
#[flux::sig(fn(i32{v: 0 < v}))]
fn needs_pos(_value: i32) {}

#[flux::trusted]
#[flux::sig(fn(i32{v: v < 10}))]
fn needs_small(_value: i32) {}

#[flux::sig(fn(i32) -> ())]
pub fn foo(x: i32) {
    needs_pos(x); //~ ERROR refinement type error
    needs_small(x); //~ ERROR refinement type error
}

#[flux::spec( fn(i32) -> () )]
pub fn foo_with_spec(x: i32) {
    needs_pos(x); //~ ERROR refinement type error
    needs_small(x); //~ ERROR refinement type error
}

#[cfg(flux_test_suggestions_applied)]
fn witness() {
    foo(5);
    foo_with_spec(5);
}
