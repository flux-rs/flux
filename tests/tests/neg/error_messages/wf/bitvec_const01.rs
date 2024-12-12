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

#[flux_rs::constant(bv_int_to_bv32(0x4567))]
pub const START: BV32 = BV32::new(0x4567);

#[flux_rs::constant(true)] //~ ERROR mismatched sorts
pub const BAD1: BV32 = BV32::new(0x4567);

#[flux_rs::constant(2+5)] //~ ERROR mismatched sorts
pub const BAD2: BV32 = BV32::new(0x4567);

#[flux_rs::sig(fn () -> BV32[BAD1])]
fn test1() -> BV32 {
    BV32::new(0x4567)
}

#[flux_rs::sig(fn () -> BV32[BAD2])]
fn test2() -> BV32 {
    BV32::new(0x4567)
}

pub const BAD3: BV32 = BV32::new(0x4567); //~ ERROR missing constant

#[flux_rs::sig(fn () -> BV32{v: v == BAD3})]
fn test3() -> BV32 {
    BV32::new(0x4567)
}
