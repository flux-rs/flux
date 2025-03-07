use flux_rs::{attrs::*, bitvec::BV32};

#[sig(fn(x: BV32) -> BV32[x + 99999999999999999])] //~ ERROR integer is not a `bitvec(32)` bit vector
pub fn test_02(x: BV32) -> BV32 {
    x + BV32::new(1)
}
