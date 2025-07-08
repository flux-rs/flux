use core::{iter::Step, ops};

use flux_attrs::*;
// The below are "default" implementations of the associated refinements
// for the `Step` trait, that we put in so that types for which no explicit
// implementation is given can be analyzed without Flux complaining about missing
// implementations. Note that the implementations are "uninterpreted" to make verification
// sound. However, you may get "false positives" if you use these defaults.

defs! {
    fn default_step_can_step_forward<T>(start: T, count: int) -> bool;
    fn default_step_step_forward<T>(start: T, count: int) -> T;
    fn default_step_size<T>(lo: T, hi: T) -> int;
}

/// We define the following associated refinements for the `Step` trait, which are then
/// used to specify the API for the `Iterator` implementation for `Range<A>`.
///  - `can_step_forward` checks if we can step forward from `start` by `count`,
///  - `step_forward` computes the new value after stepping forward from `start` by `count`,
///  - `size` computes the number of steps needed to go from `lo` to `hi
#[extern_spec(core::iter)]
trait Step {
    #![reft(
        fn can_step_forward(start: Self, count: int) -> bool {
            default_step_can_step_forward(start, count)
        }
        fn step_forward(start: Self, count: int) -> Self {
            default_step_step_forward(start, count)
        }
        fn size(lo: Self, hi: Self) -> int {
            default_step_size(lo, hi)
        }
    )]
    //
}

#[extern_spec(core::iter)]
impl Step for usize {
    #![reft(
        fn can_step_forward(start: int, count: int) -> bool  { start + count < usize::MAX }
        fn step_forward(start: int, count: int) -> int { start + count }
        fn size(lo: int, hi: int) -> int { hi - lo }
    )]
    //
}

#[extern_spec(core::iter)]
impl Step for i32 {
    #![reft(
        fn can_step_forward(start: int, count: int) -> bool  { start + count < i32::MAX }
        fn step_forward(start: int, count: int) -> int { start + count }
        fn size(lo: int, hi: int) -> int { hi - lo }
    )]
    //
}

#[extern_spec(core::ops)]
#[assoc(fn valid_item(self: Range<A>, item: A) -> bool { self.start <= item && item < self.end })]
#[assoc(fn size(self: Range<A>) -> int { <A as Step>::size(self.start, self.end) })]
#[assoc(fn done(self: Range<A>) -> bool { <A as Step>::size(self.start, self.end) <= 0})]
#[assoc(fn step(self: Range<A>, other: Range<A>) -> bool { <A as Step>::can_step_forward(self.start, 1) => other.start == <A as Step>::step_forward(self.start, 1) } )]
impl<A: Step> Iterator for ops::Range<A> {
    #[spec(
        fn(self: &mut Range<A>[@old]) -> Option<A[old.start]>[old.start < old.end]
            ensures self: Range<A>{r: (old.start < old.end => r.start == <A as Step>::step_forward(old.start, 1)) && r.end == old.end }
    )]
    fn next(&mut self) -> Option<A>;
}
