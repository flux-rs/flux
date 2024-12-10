// #![flux::defs(
//     fn is_start(x:bitvec<32>) -> bool { x == ICER_START }
// )]

// // reflect_as (fn bob(BV32[@val]) -> sort { expr-over-val })
// #[flux_rs::opaque]
// #[flux_rs::refined_by(x: bitvec<32>)]
// pub struct BV32(u32);

// #[flux_rs::trusted]
// #[flux_rs::sig(fn (x:u32) -> BV32[bv_int_to_bv32(x)])]
// const fn into_bv32(x: u32) -> BV32 {
//     BV32(x)
// }

// pub const ICER_START: BV32 = into_bv32(0xE000E180); // BV[const_mickey]

#[flux::sig_const(i32[5])]
pub const ALBERT_THE_CHIMPANZEE: i32 = {
    let mut x = 3;
    x += 1;
    x + 1
};
