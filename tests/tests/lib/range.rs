#![allow(unused)]

use core::ops::Range;

use flux_rs::extern_spec;

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::refined_by(start: Idx, end: Idx)]
struct Range<Idx> {
    #[field(Idx[start])]
    start: Idx,
    #[field(Idx[end])]
    end: Idx,
}

// #[flux_rs::extern_spec(core::ops)]
// #[generics(Self as base, T as base)]
// #[flux_rs::assoc(fn start(self: Self) -> T)]
// #[flux_rs::assoc(fn end(self: Self) -> T)]
// trait RangeBounds<T> {
//     #[flux_rs::sig(fn(&Self) -> Bound<&T>)]
//     fn start_bound(&self) -> Bound<&T>;
//     #[flux_rs::sig(fn(&Self) -> Bound<&T>)]
//     fn end_bound(&self) -> Bound<&T>;
// }

// #[flux_rs::extern_spec(core::ops)]
// #[generics(T as base)]
// #[flux_rs::assoc(fn start(self: Range<T>) -> T { self.end })]
// #[flux_rs::assoc(fn end(self: Range<T>) -> T { self.end })]
// impl<T> RangeBounds<T> for Range<T> {
//     #[flux_rs::sig(fn(&Range<T>[@r]) -> Bound<&T>[true, false])]
//     fn start_bound(&self) -> Bound<&T>;
//     #[flux_rs::sig(fn(&Range<T>[@r]) -> Bound<&T>[true, false])]
//     fn end_bound(&self) -> Bound<&T>;
// }
