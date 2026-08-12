use flux_rs::macros::detached_spec;

#[flux::opaque]
#[flux::refined_by(val: bitvec<32>)]
#[derive(PartialEq, Eq)]
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

#[flux_rs::sig(fn () -> BV32[START])]
pub fn test1() -> BV32 {
    START
}

// The `#[derive(PartialEq)]` generated `eq` reads the internal `u32` of the
// opaque `BV32`. Derive-generated code cannot be annotated directly, so we
// mark it trusted with a detached spec.
detached_spec! {
    impl std::cmp::PartialEq for BV32 {
        #[trusted]
        fn eq(&BV32[@x], other: &BV32[@y]) -> bool[x == y];
    }
}

#[flux_rs::sig(fn (BV32[@addr]) -> bool[addr == START])]
pub fn test2(address: BV32) -> bool {
    address == START
}

#[flux_rs::sig(fn (i32[@addr]) -> bool[addr == 666])]
pub fn test3(address: i32) -> bool {
    address == 666
}
