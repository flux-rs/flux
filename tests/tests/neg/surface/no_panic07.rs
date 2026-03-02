#[flux::assoc(fn foo_no_panic() -> bool)]
trait Ticks {
    #[flux::sig(fn (&Self) -> Self)]
    #[flux::no_panic_if(Self::foo_no_panic())]
    fn foo(&self) -> Self;
}

// `call_ticks_0` and `call_ticks_1` should have identical behavior, but
// right now, they don't because of the way we handle closures: closures
// only inherit their `no_panic` status from the first parent who is annotated
// with `no_panic`, effectively ignoring the `no_panic_if` annotation on `call_ticks_0`.
// Boo!
#[flux::sig(fn (_) -> ())]
#[flux::no_panic_if(true)]
fn call_ticks_0<T: Ticks>(a: T) {
    let x = || {
        a.foo(); //~ ERROR may panic
    };
}

#[flux::sig(fn (_) -> ())]
#[flux::no_panic]
fn call_ticks_1<T: Ticks>(a: T) {
    let x = || {
        a.foo(); //~ ERROR may panic
    };
}
