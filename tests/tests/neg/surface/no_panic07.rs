#[flux::assoc(fn foo_no_panic() -> bool)]
trait Ticks {
    #[flux::sig(fn (&Self) -> Self)]
    #[flux::no_panic_if(Self::foo_no_panic())]
    fn foo(&self) -> Self;
}

#[flux::no_panic]
fn call_ticks_0<T: Ticks>(a: T) {
    // this (correctly) errors
    a.foo(); //~ ERROR may panic
}

#[flux::no_panic_if(true)]
fn call_ticks_1<T: Ticks>(a: T) {
    // this (buggy) for now, does not.
    a.foo(); //~ ERROR may panic
}
