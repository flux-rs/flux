#[flux::no_panic]
fn calls_safe() {
    foo();
}

// This function is not marked as no_panic, but the syntactic analysis
// will infer its no_panic status because it only calls safe functions.
fn foo() -> i32 {
    2
}
