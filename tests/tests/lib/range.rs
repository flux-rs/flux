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
