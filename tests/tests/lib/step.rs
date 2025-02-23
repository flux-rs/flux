#![allow(unused)]
#![feature(step_trait)]

use flux_rs::attrs::*;

#[path = "option.rs"]
mod option;

use std::iter::Step;

// TODO(RJ): use default spec `true` for `can_step_forward` and `can_step_backward`

#[extern_spec(core::ops)]
trait Step {
    #![reft(
        fn can_step_forward(start: Self, count: int) -> bool;
        fn step_forward(start: Self, count: int) -> Self;
    )]
    //
}

#[extern_spec(std::iter)]
impl Step for usize {
    #![reft(
        fn can_step_forward(start: int, count: int) -> bool  { true }
        fn step_forward(start: int, count: int) -> int { start + count }
    )]
    //
}

#[flux_rs::extern_spec(std::iter)]
impl Step for i32 {
    #![reft(
        fn can_step_forward(start: int, count: int) -> bool  { true }
        fn step_forward(start: int, count: int) -> int { start + count }
    )]
    //
}
