#![flux::defs(
    fn is_start(x:bitvec<32>) -> bool { x == START }
)]

#[flux::opaque]
#[flux::refined_by(val: bitvec<32>)]
pub struct BV32(u32);

impl BV32 {
    #[flux::trusted]
    #[flux::sig(fn (x:u32) -> BV32[bv_int_to_bv32(x)])]
    const fn new(val: u32) -> Self {
        BV32(val)
    }
}

#[flux_rs::constant(BV32[int_to_bv32(0x4567)])]
pub const START: BV32 = BV32::new(0x4567);

#[flux_rs::sig(fn () -> BV32[START])]
fn test1() -> BV32 {
    BV32::new(0x4567)
}

// // USE: get the below to be SAFE
// #[flux_rs::sig(fn () -> BV32{v: is_start(v)})]
// fn test2() -> BV32 {
//     BV32::new(0x4567)
// }
