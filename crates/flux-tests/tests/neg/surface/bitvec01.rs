#![flux::defs(
      fn pow2(x:int) -> bool { pow2bv(bv_int_to_bv32(x)) }
      fn pow2bv(x:bitvec<32>) -> bool { bv_and(x, bv_sub(x, bv_int_to_bv32(1))) == bv_int_to_bv32(0) }
  )]

#[path = "../../lib/rbitvec.rs"]
mod rbitvec;
use rbitvec::Bv32;

#[flux::sig(fn (index: u32, size:u32{1 <= size && pow2(size)}) -> u32{v: v < size})]
pub fn wrap_index(index: u32, size: u32) -> u32 {
    Bv32::from_bv(Bv32::to_bv(index) & Bv32::to_bv(size)) //~ ERROR: refinement type
}
