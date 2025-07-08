#![allow(unused)]
#![feature(step_trait)]

use std::{
    iter::{Enumerate, Skip, Step, Zip},
    slice::Iter,
};

extern crate flux_core;

#[path = "iter.rs"]
mod iter;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::refined_by(n: int, inner: I)]
struct Skip<I>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::refined_by(a: A, b: B, idx: int, len: int, a_len: int)]
struct Zip<A, B>;

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::assoc(fn valid_item(self: Range<A>, item: A) -> bool { self.start <= item && item < self.end })]
#[flux_rs::assoc(fn size(self: Range<A>) -> int { <A as Step>::size(self.start, self.end) })]
#[flux_rs::assoc(fn done(self: Range<A>) -> bool { <A as Step>::size(self.start, self.end) <= 0})]
#[flux_rs::assoc(fn step(self: Range<A>, other: Range<A>) -> bool { <A as Step>::can_step_forward(self.start, 1) => other.start == <A as Step>::step_forward(self.start, 1) } )]
impl<A: Step> Iterator for Range<A> {
    #[flux_rs::sig(
        fn(self: &mut Range<A>[@old]) -> Option<A[old.start]>[old.start < old.end]
            ensures self: Range<A>{r: (old.start < old.end => r.start == <A as Step>::step_forward(old.start, 1)) && r.end == old.end }
    )]
    fn next(&mut self) -> Option<A>;
}

#[flux_rs::extern_spec(core::iter)]
#[flux_rs::assoc(fn size(r: Skip<I>) -> int { <I as Iterator>::size(r.inner) } )]
#[flux_rs::assoc(fn done(r: Skip<I>) -> bool { <I as Iterator>::done(r.inner) } )]
#[flux_rs::assoc(fn step(self: Skip<I>, other: Skip<I>) -> bool { <I as Iterator>::step(self.inner, other.inner) } )]
impl<I: Iterator> Iterator for Skip<I> {
    #[flux_rs::sig(fn(&mut Skip<I>[@n, @inner]) -> Option<I::Item>[<I as Iterator>::done(inner)])]
    fn next(&mut self) -> Option<I::Item>;
}

#[flux_rs::extern_spec(core::iter)]
// VTOCK todo: Is this really the right thing (see A::MAY_HAVE_SIDE_EFFECT)
#[flux_rs::assoc(fn size(r: Zip<A, B>) -> int { r.len })]
#[flux_rs::assoc(fn done(r: Zip<A, B>) -> bool { r.idx >= r.len && r.idx >= r.a_len })]
#[flux_rs::assoc(fn step(self: Zip<A, B>, other: Zip<A, B>) -> bool { self.idx + 1 == other.idx } )]
impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    #[flux_rs::sig(fn(&mut Zip<A, B>[@a, @b, @idx, @len, @a_len]) -> Option<_>[idx >= len || idx >= a_len])]
    fn next(&mut self) -> Option<<Zip<A, B> as Iterator>::Item>;
}
