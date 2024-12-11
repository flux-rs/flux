#![flux_rs::defs(
    fn is_start(x:bitvec<32>) -> bool { x == START }
)]

#[flux_rs::opaque]
#[flux_rs::refined_by(val: bitvec<32>)]
pub struct BV32(u32);

impl BV32 {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn (x:u32) -> BV32[bv_int_to_bv32(x)])]
    fn new(val: u32) -> Self {
        BV32(val)
    }
}

pub const START: BV32 = BV32::new(0x4567);
