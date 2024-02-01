#![feature(allocator_api)]
#![feature(associated_type_bounds)]
use std::{
    alloc::{Allocator, Global},
    ops::Index,
    slice::SliceIndex,
};

use flux_rs::extern_spec;

#[extern_spec]
#[flux::refined_by(len: int)]
struct Vec<T, A: Allocator = Global>;

#[extern_spec]
#[flux::generics(Self as base, T as base)]
#[flux::predicate{in_bounds : (Self, T) -> bool}]
trait SliceIndex<T>
where
    T: ?Sized,
{
}

#[extern_spec]
#[flux::predicate{in_bounds = |idx:int, len:int| {idx < len} }]
impl<T> SliceIndex<[T]> for usize {}

//---------------------------------------------------------------------------------------

#[extern_spec]
#[flux::generics(I as base)]
impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A> {
    // // type Output = I::Output;
    // fn index(z: &Vec<T, A>, index: I) -> &<Vec<T, A> as Index<I>>::Output;

    #[flux::sig(fn (&Vec<T,A>[@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
    fn index(z: &Vec<T, A>, index: I) -> &<I as SliceIndex<[T]>>::Output;
}

// #[extern_spec]
// impl<T> Vec<T> {
//     #[flux::sig(fn() -> Vec<T>[0])]
//     fn new() -> Vec<T>;
// }

// #[extern_spec]
// impl<T, A: Allocator> Vec<T, A> {
//     #[flux::sig(fn(self: &strg Vec<T, A>[@n], T) ensures self: Vec<T, A>[n+1])]
//     fn push(v: &mut Vec<T, A>, value: T);

//     #[flux::sig(fn(&Vec<T, A>[@n]) -> usize[n])]
//     fn len(v: &Vec<T, A>) -> usize;

//     #[flux::sig(fn(&Vec<T, A>[@n]) -> bool[n == 0])]
//     fn is_empty(v: &Vec<T, A>) -> bool;
// }

#[flux::sig(fn (&Vec<i32>[1000]) -> &i32)]
pub fn test_get0(xs: &Vec<i32>) -> &i32 {
    <Vec<i32> as Index<usize>>::index(xs, 10) //~ ERROR refinement type
}

#[flux::sig(fn (&Vec<i32>[50]) -> i32)]
pub fn test_get1(xs: &Vec<i32>) -> i32 {
    xs[10] //~ ERROR refinement type
}

// pub fn test_set(xs: &mut Vec<i32>) {
//     xs[10] = 100; //~ ERROR refinement type
// }
