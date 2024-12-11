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

// #[flux_rs::constant(BV32[int_to_bv32(0x4567)])]
pub const START: BV32 = BV32::new(0x4567);

// USE: get the below to be SAFE
#[flux_rs::sig(fn () -> BV32[START])]
fn test1() -> BV32 {
    BV32::new(0x4567)
}

// USE: get the below to be SAFE
#[flux_rs::sig(fn () -> BV32{v: is_start(v)})]
fn test2() -> BV32 {
    BV32::new(0x4567)
}

// CHECK: get the below to be UNSAFE
#[flux_rs::constant(BV32[int_to_bv32(0x456)])]
pub const BAD: BV32 = BV32::new(0x4567);

// INFER: elide the `flux_rs::constant` signature...

// #[flux::sig_const(i32[5])]
// pub const ALBERT_THE_CHIMPANZEE: i32 = {
//     let mut x = 3;
//     x += 1;
//     x + 1
// };
