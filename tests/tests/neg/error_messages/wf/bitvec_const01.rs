#[allow(dead_code)]
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

#[flux_rs::constant(4)]
pub const BAD2: BV32 = BV32::new(0x4);

#[flux_rs::sig(fn () -> BV32[BAD1])]
pub fn test1() -> BV32 {
    BV32::new(0x4567)
}

#[flux_rs::sig(fn () -> BV32[BAD2])]
pub fn test2() -> BV32 {
    BV32::new(0x4567)
}

pub const BAD3: BV32 = BV32::new(0x4567);

#[flux_rs::sig(fn () -> BV32{v: v == BAD3})] //~ ERROR constant annotation required
pub fn test3() -> BV32 {
    BV32::new(0x4567)
}

#[flux_rs::sig(fn () -> BV32{v: v == BAD3})] //~ ERROR constant annotation required
pub fn test4() -> BV32 {
    BAD3
}
