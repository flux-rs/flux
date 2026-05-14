#![allow(unused)]

use core::marker::PhantomData;

use flux_attrs::*;

union MyUnion<T> {
    ptr: *const T,
}

#[opaque]
#[refined_by(x: crate::MyUnion)]
struct UsesUnionSort<T>(PhantomData<T>);
