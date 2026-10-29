// `size_of` at a partly generic type (`W<T>`, `Option<T>`, `[T; 2]`, ...) used to ICE:
// `W<T>: Sized` is proved by a builtin impl, but `layout_of(W<T>)` fails with `TooGeneric`
// because the layout depends on `T`. The assoc refinement should stay abstract instead.
// Trigger: `mem::size_of::<W<T>>()`, whose flux-core spec returns `usize[T::size_of()]`.

// Tests for issue #1873

extern crate flux_core;

pub struct W<T>(pub T);

pub fn size_of_call<T>() -> usize {
    core::mem::size_of::<W<T>>()
}

pub fn slice_as_mut_ptr<T>(v: &mut [W<T>]) -> *mut W<T> {
    v.as_mut_ptr()
}
