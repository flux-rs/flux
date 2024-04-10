#![feature(allocator_api)]
use std::{
    alloc::{Allocator, Global},
    ops::{Index, IndexMut},
    slice::SliceIndex,
};

use flux_rs::extern_spec;

#[extern_spec]
#[flux::refined_by(len: int)]
struct Vec<T, A: Allocator = Global>;

#[extern_spec]
#[flux::generics(Self as base, T as base)]
#[flux::assoc(fn in_bounds(idx: Self, v: T) -> bool)]
trait SliceIndex<T>
where
    T: ?Sized,
{
}

#[extern_spec]
#[flux::assoc(fn in_bounds(idx:int, len:int) -> bool {idx < len} )]
impl<T> SliceIndex<[T]> for usize {}

#[extern_spec]
#[flux::generics(I as base)]
impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A> {
    #[flux::sig(fn (&Vec<T,A>[@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
    fn index(z: &Vec<T, A>, index: I) -> &<I as SliceIndex<[T]>>::Output;
}

#[extern_spec]
#[flux::generics(I as base)]
impl<T, I: SliceIndex<[T]>, A: Allocator> IndexMut<I> for Vec<T, A> {
    #[flux::sig(fn (&mut Vec<T,A>[@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
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

// ---------------------------------------------------------------------------------------

pub fn test_get0(xs: &Vec<i32>) -> &i32 {
    <Vec<i32> as Index<usize>>::index(xs, 10) //~ ERROR refinement type
}

pub fn test_get1(xs: &Vec<i32>) -> i32 {
    xs[10] //~ ERROR refinement type
}

#[flux::sig(fn (&Vec<i32>[100]) -> &i32)]
pub fn test_get2(xs: &Vec<i32>) -> &i32 {
    <Vec<i32> as Index<usize>>::index(xs, 99)
}

#[flux::sig(fn (&Vec<i32>[100]) -> i32)]
pub fn test_get3(xs: &Vec<i32>) -> i32 {
    xs[99]
}

pub fn test_set0(xs: &mut Vec<i32>) {
    xs[10] = 100; //~ ERROR refinement type
}

#[flux::sig(fn (&mut Vec<i32>[100]))]
pub fn test_set1(xs: &mut Vec<i32>) {
    xs[99] = 100;
}

pub fn test1() {
    let mut xs = Vec::<i32>::new();
    xs.push(10);
    xs.push(20);
    xs.push(30);

    xs[0] = 100;
    xs[1] = 100;
    xs[2] = 100;
    xs[10] = 100; //~ ERROR refinement type
}

pub fn test2(xs: Vec<i32>, i: usize) {
    if i < xs.len() {
        let _ = xs[i];
        let _ = xs[i + 1]; //~ ERROR refinement type
    }
}
