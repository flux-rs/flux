// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: 0 < x
// suggestion: x < 10
// The two errors must produce one non-overlapping replacement fixing both calls.
#[flux::trusted]
#[flux::sig(fn(i32{v: 0 < v}))]
fn needs_pos(_x: i32) {}

#[flux::trusted]
#[flux::sig(fn(i32{v: v < 10}))]
fn needs_small(_x: i32) {}

#[flux::sig(fn(i32) -> ())]
fn foo(x: i32) {
    needs_pos(x); //~ ERROR refinement type error
    needs_small(x); //~ ERROR refinement type error
}
