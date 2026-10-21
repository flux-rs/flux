// `const N: usize` is only known to be non-negative, nothing stronger.

use flux_attrs::*;

#[spec(fn() -> usize{v: 0 < v})]
pub fn const_pos<const N: usize>() -> usize {
    N //~ ERROR refinement type
}

pub fn const_pred<const N: usize>() -> usize {
    N - 1 //~ ERROR underflow
}

#[spec(fn() -> i32{v: 0 <= v})]
pub fn const_signed<const N: i32>() -> i32 {
    N //~ ERROR refinement type
}
