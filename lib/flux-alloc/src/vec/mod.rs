use std::{
    alloc::{Allocator, Global},
    ops::{Index, IndexMut},
    slice::SliceIndex,
};

use flux_attrs::*;

//---------------------------------------------------------------------------------------
#[extern_spec]
#[refined_by(len: int)]
#[invariant(0 <= len)]
struct Vec<T, A: Allocator = Global>;

//---------------------------------------------------------------------------------------

#[extern_spec]
impl<T> Vec<T> {
    #[flux::sig(fn() -> Vec<T>[0])]
    fn new() -> Vec<T>;
}

// FIXME(nilehmann): rustc reorganized Vec's impl blocks in nightly-2026-01-07, spreading methods
// like push, len, pop, and is_empty across multiple separate impl blocks. Flux's extern_spec system
// requires all methods in an extern spec impl to be from the same rustc impl block, and doesn't
// support multiple extern specs for the same type signature.
// 
// This temporarily disables specs for these methods, causing 4 test failures:
// - tests/pos/vec/vec00.rs
// - tests/pos/surface/iter_vec00.rs
// - tests/pos/surface/closure11.rs
// - tests/pos/surface/closure12.rs
//
// This needs to be fixed in Flux itself to support the new rustc organization.
//
// #[extern_spec]
// impl<T, A: Allocator> Vec<T, A> {
//     #[spec(fn(self: &mut Vec<T, A>[@n], T) ensures self: Vec<T, A>[n+1])]
//     fn push(v: &mut Vec<T, A>, value: T);
//
//     #[spec(fn(&Vec<T, A>[@n]) -> usize[n])]
//     fn len(v: &Vec<T, A>) -> usize;
//
//     #[spec(fn(self: &mut Vec<T, A>[@n]) -> Option<T>[n > 0] ensures self: Vec<T, A>[if n > 0 { n-1 } else { 0 }])]
//     fn pop(&mut self) -> Option<T>;
//
//     #[spec(fn(self: &Vec<T, A>[@n]) -> bool[n == 0])]
//     fn is_empty(&self) -> bool;
// }

//---------------------------------------------------------------------------------------

#[extern_spec]
impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A> {
    #[spec(fn(&Vec<T, A>[@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
    fn index(z: &Vec<T, A>, index: I) -> &<I as SliceIndex<[T]>>::Output;
}

#[extern_spec]
impl<T, I: SliceIndex<[T]>, A: Allocator> IndexMut<I> for Vec<T, A> {
    #[spec(fn(&mut Vec<T,A>[@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
    fn index_mut(z: &mut Vec<T, A>, index: I) -> &mut <I as SliceIndex<[T]>>::Output;
}

//---------------------------------------------------------------------------------------
#[extern_spec]
impl<'a, T, A: Allocator> IntoIterator for &'a Vec<T, A> {
    #[spec(fn (&Vec<T, A>[@n]) -> <&Vec<T, A> as IntoIterator>::IntoIter[0,n])]
    fn into_iter(v: &'a Vec<T, A>) -> <&'a Vec<T, A> as IntoIterator>::IntoIter;
}

#[extern_spec]
#[assoc(fn with_size(self: Self, n:int) -> bool { self.len == n })]
impl<T> FromIterator<T> for Vec<T> {}
