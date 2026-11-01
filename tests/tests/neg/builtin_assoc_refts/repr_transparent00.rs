use std::mem::MaybeUninit;

use flux_attrs::*;

pub struct NotTransparent<T>(T);

#[spec(fn(y: T) requires T::size_of() > 10)]
fn q<T>(y: T) {}

#[spec(fn(y: T) requires T::size_of() > 10)]
pub fn test00<T>(y: T) {
    q(NotTransparent(y)) //~ ERROR refinement type
}

#[spec(fn(y: T) requires T::size_of() > 5)]
pub fn test01<T>(y: T) {
    q(MaybeUninit::new(y)) //~ ERROR refinement type
}

#[repr(transparent)]
pub struct Outer<T>(NotTransparent<T>);

#[spec(fn(y: T) requires T::size_of() > 10)]
pub fn test02<T>(y: T) {
    q(Outer(NotTransparent(y))) //~ ERROR refinement type
}
