// Regression: Index::Output is a projection in the generic extern spec, but
// its refinement sort becomes unit when instantiated with f32. Weak kvars must
// not declare that argument as int and then receive mktuple0. Run with --suggestions.
#![feature(allocator_api)]

use std::{
    alloc::{Allocator, Global},
    ops::Index,
    slice::SliceIndex,
};

use flux_attrs::extern_spec;

#[extern_spec]
#[flux::refined_by(len: int)]
struct Vec<T, A: Allocator = Global>;

#[extern_spec]
#[flux::assoc(fn in_bounds(idx: Self, v: T) -> bool)]
trait SliceIndex<T: ?Sized> {}

#[extern_spec]
#[flux::assoc(fn in_bounds(idx: int, len: int) -> bool { idx < len })]
impl<T> SliceIndex<[T]> for usize {}

#[extern_spec]
impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A> {
    #[flux::sig(fn(&Vec<T, A>[@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
    fn index(v: &Vec<T, A>, index: I) -> &<I as SliceIndex<[T]>>::Output;
}

#[flux::sig(fn(&Vec<f32>[@n], usize{v: v < n}) -> f32)]
pub fn index_float(v: &Vec<f32>, index: usize) -> f32 {
    v[index]
}
