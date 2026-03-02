#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(true)]
fn foo<F: Fn(i32) -> i32>(f: F) -> i32 {
    f(3) //~ ERROR may panic
}

#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(true)]
fn foo2<F: FnOnce(i32) -> i32>(f: F) -> i32 {
    f(3) //~ ERROR may panic
}

#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(true)]
fn foo3<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    f(3) //~ ERROR may panic
}
