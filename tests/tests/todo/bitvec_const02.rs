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

pub trait Foo {
    #[flux_rs::constant(bv_int_to_bv32(0x4567))]
    const START: BV32 = BV32::new(0x4567);

    #[flux_rs::sig(fn (_) -> BV32[Self::START])]
    fn test(&self) -> BV32 {
        Self::START
    }
}

// #[flux_rs::sig(fn () -> BV32[Foo::START])]
// fn test2<A: Foo>(x: A) -> BV32 {
//     x.test()
// }
