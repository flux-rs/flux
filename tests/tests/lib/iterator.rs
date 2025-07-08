#![allow(unused)]
#![feature(step_trait)]

use std::{
    iter::{Enumerate, Skip, Step, Zip},
    ops::Range,
    slice::Iter,
};
extern crate flux_core;

#[path = "iter.rs"]
mod iter;

#[flux_rs::extern_spec(core::iter)]
#[flux_rs::assoc(fn size(r: Skip<I>) -> int { <I as Iterator>::size(r.inner) } )]
#[flux_rs::assoc(fn done(r: Skip<I>) -> bool { <I as Iterator>::done(r.inner) } )]
#[flux_rs::assoc(fn step(self: Skip<I>, other: Skip<I>) -> bool { <I as Iterator>::step(self.inner, other.inner) } )]
impl<I: Iterator> Iterator for Skip<I> {
    #[flux_rs::sig(fn(&mut Skip<I>[@n, @inner]) -> Option<I::Item>[<I as Iterator>::done(inner)])]
    fn next(&mut self) -> Option<I::Item>;
}
