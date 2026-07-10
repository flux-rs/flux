use flux_rs::{attrs::*, bitvec::BV32};

defs! {
    fn is_pow2(x: bitvec<32>) -> bool {
        (x > 0) && ((x & x - 1) == 0)
    }
}

#[sig(fn(x: BV32) requires is_pow2(x) && 8 <= x ensures x % 8 != 0)]
fn theorem_pow2_octet(x: BV32) {} //~ ERROR refinement type error
