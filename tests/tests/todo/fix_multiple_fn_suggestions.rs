// compile-flags: -Fsuggestions-z3=process
// Run with `cargo x --suggestions run tests/tests/todo/fix_multiple_fn_suggestions.rs -- -Fsuggestions-z3=process`.
#[flux::trusted]
#[flux::sig(fn(i32{v: 0 < v}))]
fn needs_pos(_x: i32) {}

#[flux::trusted]
#[flux::sig(fn(i32{v: v < 10}))]
fn needs_small(_x: i32) {}

#[flux::sig(fn(i32) -> ())]
fn foo(x: i32) {
    needs_pos(x);
    needs_small(x);
}
