#![feature(stmt_expr_attributes)]

fn okay_if_i_panic() {
    let bad_thing = |x: i32| { panic!("this is ok"); x };
    bad_thing(1);
}

// This is okay; `foo` has not been called with some `f` that panics.
#[flux::no_panic]
fn foo(f: fn(i32) -> i32) {
    f(2);
}

// This is bad, we try to call `f` with some function that _does_ panic.
#[flux::no_panic]
fn bar(f: fn(i32) -> i32) {
    f(3);
}

// Observe `main` is not annotated with `no_panic`, yet...
fn main() {
    // ...this should not be okay because `bar` requires its argument to be `no_panic`.
    bar(|x| x); //~ ERROR may panic (doesn't error right now, but we want it to)
}
