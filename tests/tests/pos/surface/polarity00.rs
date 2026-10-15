// Parameters that occur negatively in the signature of the callee are still inferred. This
// includes parameters in the output of a `fn` or closure that is passed as an input.

#[flux::trusted]
fn call<B>(f: fn() -> B) -> B {
    f()
}

#[flux::sig(fn() -> i32{v: v > 0})]
fn one() -> i32 {
    1
}

#[flux::sig(fn() -> i32{v: v > 0})]
pub fn test_fn_ptr() -> i32 {
    call(one)
}

#[flux::trusted]
fn apply<A, B, F: FnOnce(A) -> B>(x: A, f: F) -> B {
    f(x)
}

#[flux::sig(fn(i32{v: v > 0}) -> i32{v: v > 1})]
pub fn test_closure(x: i32) -> i32 {
    apply(x, |y| y + 1)
}

// `B` only appears in the clause for `F`
#[flux::trusted]
fn thunk<B, F: FnOnce() -> B>(f: F) -> B {
    f()
}

#[flux::sig(fn() -> i32{v: v > 0})]
pub fn test_thunk() -> i32 {
    thunk(|| 1)
}
