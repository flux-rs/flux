//! `#[assume_parametric]` annotations for std items used by tests in the basic suite, which
//! doesn't link against `flux-core`/`flux-alloc`. Tests that need them include this module with
//! `#[path = "../../lib/parametric_std.rs"] mod parametric_std;`.
#![allow(dead_code)]

use std::alloc::Allocator;

use flux_attrs::*;

#[extern_spec(std::boxed)]
impl<T> Box<T> {
    #[flux::assume_parametric(T)]
    fn new(x: T) -> Box<T>;
}

#[extern_spec(std::mem)]
#[flux::assume_parametric(T)]
fn drop<T>(x: T);

#[extern_spec(std::cell)]
impl<T> std::cell::UnsafeCell<T> {
    #[flux::assume_parametric(T)]
    const fn new(value: T) -> std::cell::UnsafeCell<T>;
}

#[extern_spec(std::cell)]
impl<T: ?Sized> std::cell::RefCell<T> {
    #[flux::assume_parametric(T)]
    fn borrow_mut(&self) -> std::cell::RefMut<'_, T>;
}

#[extern_spec(std::cell)]
impl<T: ?Sized> std::ops::Deref for std::cell::RefMut<'_, T> {
    #[flux::assume_parametric(T)]
    fn deref<'c>(&'c self) -> &'c T;
}

#[extern_spec(std::option)]
impl<T> Option<T> {
    #[flux::assume_parametric(T)]
    fn unwrap(self) -> T;

    #[flux::assume_parametric(T, U, F)]
    fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U>;
}

#[extern_spec(std::option)]
impl<T> IntoIterator for Option<T> {
    #[flux::assume_parametric(T)]
    fn into_iter(self) -> std::option::IntoIter<T>;
}

#[extern_spec(std::option)]
impl<T> std::ops::Try for Option<T> {
    #[flux::assume_parametric(T)]
    fn branch(
        self,
    ) -> std::ops::ControlFlow<
        <Option<T> as std::ops::Try>::Residual,
        <Option<T> as std::ops::Try>::Output,
    >;
}

#[extern_spec(std::option)]
impl<T> std::ops::FromResidual<Option<std::convert::Infallible>> for Option<T> {
    #[flux::assume_parametric(T)]
    fn from_residual(residual: Option<std::convert::Infallible>) -> Option<T>;
}

#[extern_spec(std::result)]
impl<T, E> Result<T, E> {
    #[flux::assume_parametric(T, E, U, F)]
    fn map<U, F: FnOnce(T) -> U>(self, op: F) -> Result<U, E>;
}

#[extern_spec(std::result)]
impl<T, E> std::ops::Try for Result<T, E> {
    #[flux::assume_parametric(T, E)]
    fn branch(
        self,
    ) -> std::ops::ControlFlow<
        <Result<T, E> as std::ops::Try>::Residual,
        <Result<T, E> as std::ops::Try>::Output,
    >;
}

#[extern_spec(std::result)]
impl<T, E, F: From<E>> std::ops::FromResidual<Result<std::convert::Infallible, E>>
    for Result<T, F>
{
    #[flux::assume_parametric(T)]
    fn from_residual(residual: Result<std::convert::Infallible, E>) -> Result<T, F>;
}

#[extern_spec(std::vec)]
impl<T> Vec<T> {
    #[flux::assume_parametric(T)]
    fn new() -> Vec<T>;
}

#[extern_spec(std::vec)]
impl<T, A: Allocator> Vec<T, A> {
    #[flux::assume_parametric(T)]
    fn push(v: &mut Vec<T, A>, value: T);
}

#[extern_spec(std::vec)]
impl<T, A: Allocator> IntoIterator for Vec<T, A> {
    #[flux::assume_parametric(T)]
    fn into_iter(self) -> <Vec<T, A> as IntoIterator>::IntoIter;
}

#[extern_spec(std::vec)]
impl<'a, T, A: Allocator> IntoIterator for &'a Vec<T, A> {
    #[flux::assume_parametric(T)]
    fn into_iter(v: &'a Vec<T, A>) -> <&'a Vec<T, A> as IntoIterator>::IntoIter;
}

#[extern_spec(std::vec)]
impl<T, A: Allocator> Iterator for std::vec::IntoIter<T, A> {
    #[flux::assume_parametric(T)]
    fn next(&mut self) -> Option<T>;
}

#[extern_spec(std::slice)]
impl<'a, T> Iterator for std::slice::Iter<'a, T> {
    #[flux::assume_parametric(T)]
    fn next(&mut self) -> Option<&'a T>;
}

#[extern_spec]
impl<T> [T] {
    #[flux::assume_parametric(T)]
    fn len(&self) -> usize;

    #[flux::assume_parametric(T)]
    fn first(&self) -> Option<&T>;

    #[flux::assume_parametric(T)]
    fn first_mut(&mut self) -> Option<&mut T>;

    #[flux::assume_parametric(T)]
    fn split_at(&self, mid: usize) -> (&[T], &[T]);

    #[flux::assume_parametric(T)]
    fn split_at_mut(&mut self, mid: usize) -> (&mut [T], &mut [T]);
}
