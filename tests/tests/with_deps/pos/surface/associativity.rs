// Test operators are parsed with the correct associativity
use flux_rs::{attrs::*, bitvec::BV32};

#[sig(fn() -> i32[2 / 2 * 2])]
fn test00() -> i32 {
    2
}

#[sig(fn() -> BV32[1_000_000_000 - 3_500_000_000 + 2_000_000_000])]
fn test01() -> BV32 {
    BV32::new(3_794_967_296)
}

#[sig(fn() -> bool[false => true => false])]
fn test02() -> bool {
    true
}
