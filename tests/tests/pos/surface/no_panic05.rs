// This is bad, we try to call `f` with some function that _does_ panic.
#[flux::no_panic]
#[flux::sig(fn(f: F) -> i32 requires F::no_panic())]
fn bar<F: Fn(i32) -> i32>(f: F) -> i32 {
    f(3) // check here: is the type of `f` such that it cannot panic? Yes! So `bar` is not in trouble.
}

#[flux::no_panic]
fn foo() {
    // This is OK because `foo` is marked `no_panic`, therefore all closures within `foo` are also no_panic.
    bar(|x| blah(3));
}

#[flux::no_panic]
fn blah(x: i32) -> i32 {
    3
}
