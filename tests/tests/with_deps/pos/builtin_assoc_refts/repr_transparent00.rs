extern crate flux_core;

use std::{marker::PhantomData, mem::MaybeUninit};

use flux_attrs::*;

#[repr(transparent)]
pub struct Inner<T> {
    x: T,
}

#[repr(transparent)]
pub struct Outer<T>(Inner<T>);

#[repr(transparent)]
pub struct W<T, U>(PhantomData<U>, T, ());

#[spec(fn(y: T) requires T::size_of() > 10 && T::align_of() == 8)]
fn q<T>(y: T) {}

#[spec(fn(y: T) requires T::size_of() > 10 && T::align_of() == 8)]
pub fn test01<T>(y: T) {
    q(Outer(Inner { x: y }))
}

#[spec(fn(y: T) requires T::size_of() > 10 && T::align_of() == 8)]
pub fn test02<T>(y: T) {
    q(MaybeUninit::new(y))
}

#[spec(fn(y: T) requires T::size_of() > 10 && T::align_of() == 8)]
pub fn test03<T, U>(y: T) {
    q(W::<MaybeUninit<T>, U>(PhantomData, MaybeUninit::new(y), ()))
}

#[spec(fn() -> bool[true])]
pub fn test04<T>() -> bool {
    std::mem::size_of::<T>() == std::mem::size_of::<MaybeUninit<T>>()
}

#[spec(fn() -> bool[true])]
pub fn test05<T>() -> bool {
    std::mem::align_of::<T>() == std::mem::align_of::<MaybeUninit<T>>()
}
