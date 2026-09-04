//! Check that slice length bounds are assumed when overflow checking is enabled.

#![flux::opts(check_overflow = "strict")]

#[flux::sig(fn(&[T][@len]) ensures T::size_of() * len <= isize::MAX)]
fn generic<T>(_: &[T]) {}

#[flux::sig(fn(&[()][@len]) ensures len <= usize::MAX)]
fn zst(_: &[()]) {}
