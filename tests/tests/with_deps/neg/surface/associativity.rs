// These tests produce the result with the wrong associavitiy
use flux_rs::{attrs::*, bitvec::BV32};

#[sig(fn() -> i32[2 / 2 * 2])]
fn test00() -> i32 {
    0 //~ ERROR refinement type error
}

#[sig(fn() -> BV32[1_000_000_000 - 3_500_000_000 + 2_000_000_000])]
fn test01() -> BV32 {
    BV32::new(4_089_934_592) //~ ERROR refinement type error
}

#[sig(fn() -> bool[false => true => false])]
fn test02() -> bool {
    false //~ ERROR refinement type error
}
