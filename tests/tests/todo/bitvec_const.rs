#![flux::defs(
    fn is_start(x:bitvec<32>) -> bool { x == ICER_START }
)]

#[flux_rs::opaque]
#[flux_rs::refined_by(x: bitvec<32>)]
pub struct BV32(u32);

#[flux_rs::trusted]
#[flux_rs::sig(fn (x:u32) -> BV32[bv_int_to_bv32(x)])]
const fn into_bv32(x: u32) -> BV32 {
    BV32(x)
}

pub const ICER_START: BV32 = into_bv32(0xE000E180);
