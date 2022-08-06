#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/range.rs"]
mod range;
use range::{Rng, RngIter};

#[flux::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

pub fn test_next() {
    let mut rng = RngIter::new(10, 15);
    while let Some(val) = rng.next() {
        assert(10 <= val && val < 15)
    }
}

// pub fn test_for() {
//     for val in Rng::new(110, 115) {
//         assert(110 <= val && val < 115)
//     }
// }

// {
//     bb9: [a0: int, a1: int, a2: int].
//         {_1: RngIter<@a0, @a1>, _3.0: i32<a2>, _6: i32<a2>, _7: bool{*}},
//     bb2: [].
//         {_1: RngIter{*}},
//     bb11: [a0: int, a1: int].
//         {_1: RngIter<@a0, @a1>, _3: Option<i32{a0 ≤ ^0.0 ∧ ^0.0 < a1}>}
// }

// {
//     bb9: [a0: int] ∃ a1: bool.
//         {_1: RngIter<10, 15>, _3.0: i32<a0>, _6: i32<a0>, _7: bool<a1>},
//     bb2: [] ∃ .
//         {_1: RngIter<10, 15>},
//     bb11: [] ∃ .
//         {_1: RngIter<@10, @15>, _3: Option<i32{10 ≤ ^0.0 ∧ ^0.0 < 15}>}
// }
