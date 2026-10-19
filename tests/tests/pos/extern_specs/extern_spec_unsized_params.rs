//@aux-build:extern_spec_unsized_params_aux.rs

// Extern specs for impls whose type parameters are not `Sized`.
#![feature(sized_hierarchy)]

extern crate extern_spec_unsized_params_aux;

use std::marker::PointeeSized;

use extern_spec_unsized_params_aux::{Answer, MaybeUnsized, Pointee};
use flux_attrs::*;

#[extern_spec]
impl<T: ?Sized> MaybeUnsized<T> {
    #[spec(fn(&Self) -> usize[42])]
    fn answer(&self) -> usize;
}

#[extern_spec]
impl<T: PointeeSized> Pointee<T> {
    #[spec(fn(&Self) -> usize[42])]
    fn answer(&self) -> usize;
}

#[extern_spec]
impl<T: ?Sized> Answer for MaybeUnsized<T> {
    #[spec(fn(&Self) -> usize[42])]
    fn answer_trait(&self) -> usize;
}

#[spec(fn(&MaybeUnsized<[i32]>) -> usize[42])]
pub fn test_unsized(x: &MaybeUnsized<[i32]>) -> usize {
    x.answer()
}

#[spec(fn(&Pointee<str>) -> usize[42])]
pub fn test_pointee_sized(x: &Pointee<str>) -> usize {
    x.answer()
}

#[spec(fn(&MaybeUnsized<[i32]>) -> usize[42])]
pub fn test_trait_impl(x: &MaybeUnsized<[i32]>) -> usize {
    x.answer_trait()
}
