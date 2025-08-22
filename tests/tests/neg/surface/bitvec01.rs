#![flux::defs(
      fn pow2(x:int) -> bool { pow2bv(bv_int_to_bv32(x)) }
      fn pow2bv(x:bitvec<32>) -> bool { bv_and(x, bv_sub(x, bv_int_to_bv32(1))) == bv_int_to_bv32(0) }
  )]

use flux_rs::bitvec::BV32;

#[flux::sig(fn (index: u32, size:u32{1 <= size && pow2(size)}) -> u32{v: v < size})]
pub fn wrap_index(index: u32, size: u32) -> u32 {
    (BV32::new(index) & BV32::new(size)).into() //~ ERROR: refinement type
}
