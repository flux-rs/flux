extern crate alloc;

use std::mem::MaybeUninit;

use flux_attrs::*;

/// This function is used internally by the `vec![...]` macro. We must give it a spec so we know, e.g.,
/// `vec![1, 2, 3]` has length 3.
///
/// https://github.com/rust-lang/rust/blob/a8a1e6fd9df2e094d6f09c0d57991508680acc1c/library/alloc/src/boxed.rs#L266
#[extern_spec(alloc::boxed)]
#[spec(fn(Box<MaybeUninit<[T; N]>>) -> Vec<T>[N])]
fn box_assume_init_into_vec_unsafe<T, const N: usize>(b: Box<MaybeUninit<[T; N]>>) -> Vec<T>;
