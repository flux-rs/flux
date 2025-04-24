use std::{
    alloc::{Allocator, Global},
    ops::{Index, IndexMut},
    slice::{Iter, SliceIndex},
};

use flux_rs::extern_spec;

#[extern_spec]
#[flux::refined_by(len: int)]
struct Vec<T, A: Allocator = Global>;

#[extern_spec]
#[flux::assoc(fn in_bounds(idx: Self, v: T) -> bool)]
trait SliceIndex<T>
where
    T: ?Sized,
{
}

#[extern_spec]
#[flux::assoc(fn in_bounds(idx: int, len: int) -> bool {idx < len} )]
impl<T> SliceIndex<[T]> for usize {}

#[extern_spec]
#[flux::generics(I as base)]
impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A> {
    #[flux::sig(fn(&Vec<T, A>[@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
    fn index(z: &Vec<T, A>, index: I) -> &<I as SliceIndex<[T]>>::Output;
}

#[extern_spec]
#[flux::generics(I as base)]
impl<T, I: SliceIndex<[T]>, A: Allocator> IndexMut<I> for Vec<T, A> {
    #[flux::sig(fn(&mut Vec<T,A>[@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
    fn index_mut(z: &mut Vec<T, A>, index: I) -> &mut <I as SliceIndex<[T]>>::Output;
}

//---------------------------------------------------------------------------------------

#[extern_spec]
impl<T> Vec<T> {
    #[flux::sig(fn() -> Vec<T>[0])]
    fn new() -> Vec<T>;
}

#[extern_spec]
impl<T, A: Allocator> Vec<T, A> {
    #[flux::sig(fn(self: &strg Vec<T, A>[@n], T) ensures self: Vec<T, A>[n+1])]
    fn push(v: &mut Vec<T, A>, value: T);

    #[flux::sig(fn(&Vec<T, A>[@n]) -> usize[n])]
    fn len(v: &Vec<T, A>) -> usize;
}

#[extern_spec]
impl<'a, T, A: Allocator> IntoIterator for &'a Vec<T, A> {
    #[flux::sig(fn (&Vec<T, A>[@n]) -> <&Vec<T, A> as IntoIterator>::IntoIter[0,n])]
    fn into_iter(v: &'a Vec<T, A>) -> <&'a Vec<T, A> as IntoIterator>::IntoIter;
}

#[extern_spec]
#[flux::assoc(fn with_size(self: Self, n:int) -> bool { self.len == n })]
impl<T> FromIterator<T> for Vec<T> {}
