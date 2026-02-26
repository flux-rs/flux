#[flux_rs::sig(fn(f: F) -> i32)]
#[flux_rs::no_panic_if(F::no_panic())]
fn foo<F: FnOnce(i32) -> i32>(f: F) -> i32 {
    f(3)
}
