#![allow(unused)]

use core::marker::PhantomData;

use flux_attrs::*;

union MyUnion {
    ptr: *const i32,
}

#[opaque]
#[refined_by(x: crate::MyUnion)]
struct UsesUnionSort<T>(PhantomData<T>);
