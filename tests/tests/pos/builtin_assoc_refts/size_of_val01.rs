use std::mem::MaybeUninit;

use flux_attrs::*;

// Regression test: normalizing `MetaSized::size_of_val` for a *sized* type that mentions a generic
// parameter (e.g. `MaybeUninit<T>`) rewrites it to `<ty as Sized>::size_of()`. The layout of such a
// type is not known, so the alias must stay uninterpreted instead of panicking on
// `layout_of(..).unwrap()` with `TooGeneric`.

#[trusted]
#[spec(fn(m: usize) -> usize[T::size_of_val(m)])]
fn size_of_val<T: ?Sized>(_m: usize) -> usize {
    0
}

#[trusted]
#[spec(fn(m: usize) -> usize[T::align_of_val(m)])]
fn align_of_val<T: ?Sized>(_m: usize) -> usize {
    0
}

struct Wrap<T> {
    x: T,
    tag: u8,
}

// Sized types ignore the metadata, even when their layout is generic.
#[spec(fn(m: usize, n: usize) -> bool[true])]
fn maybe_uninit<T>(m: usize, n: usize) -> bool {
    size_of_val::<MaybeUninit<T>>(m) == size_of_val::<MaybeUninit<T>>(n)
        && align_of_val::<MaybeUninit<T>>(m) == align_of_val::<MaybeUninit<T>>(n)
}

#[spec(fn(m: usize, n: usize) -> bool[true])]
fn result<T, E>(m: usize, n: usize) -> bool {
    size_of_val::<Result<T, E>>(m) == size_of_val::<Result<T, E>>(n)
}

#[spec(fn(m: usize, n: usize) -> bool[true])]
fn adt<T>(m: usize, n: usize) -> bool {
    size_of_val::<Wrap<T>>(m) == size_of_val::<Wrap<T>>(n)
}

#[spec(fn(m: usize, n: usize) -> bool[true])]
fn tuple<T>(m: usize, n: usize) -> bool {
    size_of_val::<(T, u8)>(m) == size_of_val::<(T, u8)>(n)
}
