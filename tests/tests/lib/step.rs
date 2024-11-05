#![allow(unused)]
#![feature(step_trait)]

#[path = "option.rs"]
mod option;

use std::iter::Step;

// TODO(RJ): use default spec `true` for `can_step_forward` and `can_step_backward`

#[flux_rs::extern_spec(core::ops)]
#[generics(Self as base)]
#[flux_rs::assoc(fn steps_between(start: Self, end: Self) -> bool )]
#[flux_rs::assoc(fn can_step_forward(start: Self, count: int) -> bool)]
#[flux_rs::assoc(fn step_forward(start: Self, count: int) -> Self )]
#[flux_rs::assoc(fn can_step_backward(start: Self, count: int) -> bool)]
#[flux_rs::assoc(fn step_backward(start: Self, count: int) -> Self )]
trait Step {
    #[flux_rs::sig(fn(&Self[@start], &Self[@end]) -> Option<usize>[<Self as Step>::steps_between(start, end)])]
    fn steps_between(start: &Self, end: &Self) -> Option<usize>;

    #[flux_rs::sig(fn(Self[@start], usize[@n]) -> Option<Self>[<Self as Step>::can_step_forward(start, n)])]
    fn forward_checked(start: Self, count: usize) -> Option<Self>;

    #[flux_rs::sig(fn(Self[@start], usize[@n]) -> Option<Self>[<Self as Step>::can_step_backward(start, n)])]
    fn backward_checked(start: Self, count: usize) -> Option<Self>;
}

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::assoc(fn steps_between(start: int, end: int) -> bool { start <= end } )]
// #[flux_rs::assoc(fn can_step_forward(start: int, count: int) -> bool { start + count <= usize::MAX } )]
// #[flux_rs::assoc(fn can_step_backward(start: int, count: int) -> bool { start - count >= usize::MIN } )]
#[flux_rs::assoc(fn can_step_forward(start: int, count: int) -> bool  { true } )]
#[flux_rs::assoc(fn can_step_backward(start: int, count: int) -> bool { true } )]
#[flux_rs::assoc(fn step_forward(start: int, count: int) -> int { start + count } )]
#[flux_rs::assoc(fn step_backward(start: int, count: int) -> int { start - count } )]
impl Step for usize {
    #[sig(fn(&usize[@start], &usize[@end]) -> Option<usize[end - start]>[start < end])]
    fn steps_between(start: &usize, end: &usize) -> Option<usize>;

    #[sig(fn(usize[@start], usize[@n]) -> Option<usize[start + n]>[start + n <= usize::MAX])]
    fn forward_checked(start: usize, count: usize) -> Option<usize>;

    #[sig(fn(usize[@start], usize[@n]) -> Option<usize[start - n]>[start - n >= usize::MIN])]
    fn backward_checked(start: usize, count: usize) -> Option<usize>;
}

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::assoc(fn steps_between(start: int, end: int) -> bool { start <= end } )]
// #[flux_rs::assoc(fn can_step_forward(start: int, count: int) -> bool { start + count <= i32::MAX } )]
// #[flux_rs::assoc(fn can_step_backward(start: int, count: int) -> bool { start - count >= i32::MIN } )]
#[flux_rs::assoc(fn can_step_forward(start: int, count: int) -> bool  { true } )]
#[flux_rs::assoc(fn can_step_backward(start: int, count: int) -> bool { true } )]
#[flux_rs::assoc(fn step_forward(start: int, count: int) -> int { start + count } )]
#[flux_rs::assoc(fn step_backward(start: int, count: int) -> int { start - count } )]
impl Step for i32 {
    #[sig(fn(&i32[@start], &i32[@end]) -> Option<usize[end - start]>[start < end])]
    fn steps_between(start: &i32, end: &i32) -> Option<usize>;

    #[sig(fn(i32[@start], usize[@n]) -> Option<i32[start + n]>[start + n <= i32::MAX])]
    fn forward_checked(start: i32, count: usize) -> Option<i32>;

    #[sig(fn(i32[@start], usize[@n]) -> Option<i32[start - n]>[start - n >= i32::MIN])]
    fn backward_checked(start: i32, count: usize) -> Option<i32>;
}
