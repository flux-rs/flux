use std::{
    alloc::{Allocator, Global},
    // ops::{Index, IndexMut},
    // slice::{Iter, SliceIndex},
};

use flux_attrs::*;

#[extern_spec]
#[refined_by(len: int)]
struct Vec<T, A: Allocator = Global>;

#[extern_spec]
impl<T> Vec<T> {
    #[flux::sig(fn() -> Vec<T>[0])]
    fn new() -> Vec<T>;
}

#[extern_spec]
impl<T, A: Allocator> Vec<T, A> {
    #[flux::sig(fn(self: &mut Vec<T, A>[@n], T) ensures self: Vec<T, A>[n+1])]
    fn push(v: &mut Vec<T, A>, value: T);

    #[flux::sig(fn(&Vec<T, A>[@n]) -> usize[n])]
    fn len(v: &Vec<T, A>) -> usize;

    #[flux::sig(fn(self: &mut Vec<T, A>[@n]) -> Option<T> ensures self: Vec<T, A>[if n > 0 { n-1 } else { 0 }])]
    fn pop(&mut self) -> Option<T>;
}
