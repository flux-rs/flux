use flux_rs::{attrs::*, bitvec::BV32};

#[sig(fn(x: BV32) -> BV32[bv_add(x, bv_int_to_bv32(1))])]
pub fn test_00(x: BV32) -> BV32 {
    x + BV32::new(1)
}

#[sig(fn(x: BV32) -> BV32[x + bv_int_to_bv32(1)])]
pub fn test_01(x: BV32) -> BV32 {
    x + BV32::new(1)
}

#[sig(fn(x: BV32) -> BV32[x + 1])]
pub fn test_02(x: BV32) -> BV32 {
    x + BV32::new(1)
}

#[sig(fn(x: i32) -> i32[x + (1 + 2)])]
pub fn test_03(x: i32) -> i32 {
    x + 3
}
