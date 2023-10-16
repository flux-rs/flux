//! Check that we don't assume invariants under a generic type argument.

struct S<T> {
    x: T,
}

// We don't assume `n >= 0` from the `u32[n]` inside `S`, that would be unsound in general.
#[flux::sig(fn(i32[@n], S<u32[n]>))]
fn test(x: i32, _: S<u32>) {
    assert(x >= 0); //~ERROR refinement type error
}

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}
