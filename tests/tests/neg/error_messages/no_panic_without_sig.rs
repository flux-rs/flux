#[flux::no_panic_if(true)] //~ ERROR: `no_panic_if` attribute requires a `sig` annotation on the same item
fn my_fn() -> i32 {
    3
}
