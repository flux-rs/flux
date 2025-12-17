#![allow(unused)]

use flux_rs::attrs::*;

defs! {
    #[recursive]
    fn sum_to(n: int) -> int {
        if n <= 0 {
            0
        } else {
            n + sum_to(n - 1)
        }
    }
}

#[flux::opts(ple = "true")]
#[spec(fn () -> usize[sum_to(5)])]
fn test_sum_to() -> usize {
    16 //~ ERROR refinement type error
}
