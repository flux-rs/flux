#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(F::no_panic())]
fn foo<F: Fn(i32) -> i32>(f: F) -> i32 {
    f(3)
}

#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(F::no_panic())]
fn foo2<F: FnOnce(i32) -> i32>(f: F) -> i32 {
    f(3)
}

#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(F::no_panic())]
fn foo3<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    f(3)
}
