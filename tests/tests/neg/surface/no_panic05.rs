
// This is bad, we try to call `f` with some function that _does_ panic.
#[flux::no_panic]
#[flux::sig(f: fn(i32) -> i32 {v: i32 | true} ) -> i32 requires F::no_panic()]
fn bar<F: Fn(i32) -> i32>(f: F) -> i32) {
    f(3); // check here: is the type of `f` such that it cannot panic? Yes! So `bar` is not in trouble.
}

#[flux::no_panic]
fn foo() {
    // This is fine because `blah` never gets called.
    let blah = |x| { panic!("blah") };

    // the line below: `foo` is in trouble because we've promised that `foo` can't panic.
    // because of this promise, the argument to `bar` must be a function that cannot panic.
    // there may be some sort of analysis that can prove this, but we'll need to merge #1387 to get that infrastructure.
    bar(|x| if x == 3 { panic!("bad") } else { x + 1 }); //~ ERROR: may panic
}

