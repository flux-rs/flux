// The layout of a `repr(transparent)` type is the layout of its only non-1-ZST field, even when
// the layout itself depends on generic parameters.

use std::{marker::PhantomData, mem::MaybeUninit};

use flux_attrs::*;

#[repr(transparent)]
struct Wrapper<T, U> {
    val: T,
    _marker: PhantomData<U>,
}

// An unsized `repr(transparent)` type.
#[repr(transparent)]
struct Slice<T>([T]);

#[spec(fn() requires T::size_of() == 8 && T::align_of() == 8)]
fn requires_layout_8<T>() {}

#[spec(fn() requires T::size_of() == U::size_of() && T::align_of() == U::align_of())]
fn requires_same_layout<T, U>() {}

#[spec(fn(m: usize, size: usize, align: usize)
    requires T::size_of_val(m) == size && T::align_of_val(m) == align)]
fn requires_layout_val<T: ?Sized>(_m: usize, _size: usize, _align: usize) {}

#[spec(fn() requires T::size_of() == 8 && T::align_of() == 8)]
fn test_known<T>() {
    requires_layout_8::<MaybeUninit<T>>();
    requires_layout_8::<Wrapper<T, String>>();
    // Nested: `Wrapper` -> `MaybeUninit` -> `ManuallyDrop` -> `T`.
    requires_layout_8::<Wrapper<MaybeUninit<T>, T>>();
}

fn test_same<T>() {
    requires_same_layout::<MaybeUninit<T>, T>();
    requires_same_layout::<Wrapper<T, u64>, T>();
}

// Sized `repr(transparent)` types go through `size_of_val` -> `size_of` -> the field.
#[spec(fn(m: usize) requires T::size_of() == 8 && T::align_of() == 4)]
fn test_val_sized<T>(m: usize) {
    requires_layout_val::<MaybeUninit<T>>(m, 8, 4);
}

// Unsized `repr(transparent)` types: `Slice<T>` has the layout of `[T]`.
#[spec(fn(m: usize) requires T::size_of() == 4 && T::align_of() == 4)]
fn test_val_unsized<T>(m: usize) {
    requires_layout_val::<Slice<T>>(m, m * 4, 4);
}
