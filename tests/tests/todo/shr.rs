use std::ops::Range;

use flux_rs::extern_spec;

#[extern_spec]
#[flux::refined_by(lo: Idx, hi: Idx)]
struct Range<Idx>;

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test_loop0() -> i32 {
    for i in 10..20 {
        assert(10 <= i);
    }
    110
}

// pub fn test_loop<const N: usize>(arr: &[i32; N]) -> i32 {
//     let mut x = 0;
//     for i in 1..N {
//         assert(1 <= i);
//         // assert(i < N);
//         // x += arr[i];
//     }
//     x
// }
