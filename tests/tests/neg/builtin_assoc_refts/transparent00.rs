use std::mem::MaybeUninit;

use flux_attrs::*;

struct NotTransparent<T> {
    val: T,
}

#[spec(fn() requires T::size_of() == 8)]
fn requires_size_8<T>() {}

#[spec(fn() requires T::size_of() == U::size_of())]
fn requires_same_size<T, U>() {}

#[spec(fn() requires T::size_of() == 4)]
fn test_wrong_size<T>() {
    requires_size_8::<MaybeUninit<T>>(); //~ ERROR refinement type
}

// The layout of a type that is not `repr(transparent)` stays unknown.
fn test_not_transparent<T>() {
    requires_same_size::<NotTransparent<T>, T>(); //~ ERROR refinement type
}
