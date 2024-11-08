#![allow(unused)]
#![feature(step_trait)]

use std::{
    iter::{Enumerate, Skip, Step, Zip},
    slice::Iter,
};

#[path = "step.rs"]
mod step;

#[path = "range.rs"]
mod range;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::refined_by(idx: int, inner: I)]
struct Enumerate<I>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::refined_by(n: int, inner: I)]
struct Skip<I>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::refined_by(a: A, b: B, idx: int, len: int, a_len: int)]
struct Zip<A, B>;

#[flux_rs::extern_spec(std::slice)]
#[flux_rs::refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::generics(Self as base)]
#[flux_rs::assoc(fn done(self: Self) -> bool  )]
#[flux_rs::assoc(fn step(self: Self, other: Self) -> bool )]
trait Iterator {
    #[flux_rs::sig(fn(self: &strg Self[@curr_s]) -> Option<Self::Item>[!<Self as Iterator>::done(curr_s)] ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<Self::Item>;
}

#[flux_rs::extern_spec(core::ops)]
#[generics(A as base)]
#[flux_rs::assoc(fn done(r: Range<A>) -> bool { r.start == r.end } )]
#[flux_rs::assoc(fn step(self: Range<A>, other: Range<A>) -> bool { <A as Step>::can_step_forward(self.start, 1) => other.start == <A as Step>::step_forward(self.start, 1) } )]
impl<A: Step> Iterator for Range<A> {
    #[flux_rs::sig(
        fn(self: &strg Range<A>[@old_range]) -> Option<A[old_range.start]>[old_range.start < old_range.end]
            ensures self: Range<A>{r: (<A as Step>::can_step_forward(old_range.start, 1) && old_range.start < old_range.end)=> (r.start == <A as Step>::step_forward(old_range.start, 1) && r.end == old_range.end) }
    )]
    fn next(&mut self) -> Option<A>;
}

#[flux_rs::extern_spec(std::slice)]
#[flux_rs::assoc(fn done(x: Iter) -> bool { x.idx >= x.len })]
#[flux_rs::assoc(fn step(x: Iter, y: Iter) -> bool { x.idx + 1 == y.idx && x.len == y.len})]
impl<'a, T> Iterator for Iter<'a, T> {
    #[flux_rs::sig(fn(self: &strg Iter<T>[@curr_s]) -> Option<_>[curr_s.idx < curr_s.len] ensures self: Iter<T>{next_s: curr_s.idx + 1 == next_s.idx && curr_s.len == next_s.len})]
    fn next(&mut self) -> Option<&'a T>;
}

#[flux_rs::extern_spec(core::iter)]
#[generics(I as base)]
#[flux_rs::assoc(fn done(r: Enumerate<I>) -> bool { <I as Iterator>::done(r.inner) } )]
#[flux_rs::assoc(fn step(self: Enumerate<I>, other: Enumerate<I>) -> bool { self.idx + 1 == other.idx } )]
impl<I: Iterator> Iterator for Enumerate<I> {
    #[flux_rs::sig(fn(&mut Enumerate<I>[@idx, @inner]) -> Option<(usize[idx + 1], I::Item)>[<I as Iterator>::done(inner)])]
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>;
}

#[flux_rs::extern_spec(core::iter)]
#[generics(I as base)]
#[flux_rs::assoc(fn done(r: Skip<I>) -> bool { <I as Iterator>::done(r.inner) } )]
#[flux_rs::assoc(fn step(self: Skip<I>, other: Skip<I>) -> bool { <I as Iterator>::step(self.inner, other.inner) } )]
impl<I: Iterator> Iterator for Skip<I> {
    #[flux_rs::sig(fn(&mut Skip<I>[@n, @inner]) -> Option<I::Item>[<I as Iterator>::done(inner)])]
    fn next(&mut self) -> Option<I::Item>;
}

#[flux_rs::extern_spec(core::iter)]
#[generics(A as base, B as base)]
// VTOCK todo: Is this really the right thing (see A::MAY_HAVE_SIDE_EFFECT)
#[flux_rs::assoc(fn done(r: Zip<A, B>) -> bool { r.idx >= r.len && r.idx >= r.a_len })]
#[flux_rs::assoc(fn step(self: Zip<A, B>, other: Zip<A, B>) -> bool { self.idx + 1 == other.idx } )]
impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    #[flux_rs::sig(fn(&mut Zip<A, B>[@a, @b, @idx, @len, @a_len]) -> Option<_>[idx >= len || idx >= a_len])]
    fn next(&mut self) -> Option<<Zip<A, B> as Iterator>::Item>;
}

#[flux_rs::extern_spec(std::iter)]
#[generics(Self as base)]
trait IntoIterator {
    #[flux_rs::sig(fn(self: Self) -> Self::IntoIter)]
    fn into_iter(self) -> Self::IntoIter
    where
        Self: Sized;
}

#[flux_rs::extern_spec(core::ops)]
#[generics(I as base)]
impl<I: Iterator> IntoIterator for I {
    #[flux_rs::sig(fn(self: I[@s]) -> I[s])]
    fn into_iter(self) -> I;
}
