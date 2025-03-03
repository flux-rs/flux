use flux_rs::{attrs::*, bitvec::BV32};

// (0) #[sig(fn(x: BV32) -> BV32[bv_add(x, bv_int_to_bv32(1))])] // (0)
// #[sig(fn(x: BV32) -> BV32[x + 1])]   // (2)

#[sig(fn(x: BV32) -> BV32[x + bv_int_to_bv32(1)])] // (1)
pub fn test(x: BV32) -> BV32 {
    x + BV32::new(1)
}
