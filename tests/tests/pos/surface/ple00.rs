#![allow(unused)]

use flux_rs::attrs::*;

defs! {
    #[recursive]
    fn sum_to(n: int) -> int {
        if n <= 0 { 0 } else { n + sum_to(n - 1) }
    }
}

#[flux::opts(ple = "true")]
#[spec(fn () -> usize[sum_to(5)])]
fn test_sum_to() -> usize {
    15
}

#[flux::opts(ple = "true")]
#[spec(fn (n:usize) -> usize[sum_to(n)])]
fn sum_usize(n: usize) -> usize {
    if n <= 0 { 0 } else { n + sum_usize(n - 1) }
}
