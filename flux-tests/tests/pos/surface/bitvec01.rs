#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs(
      fn pow2(x:int) -> bool { pow2bv(int_to_bv32(x)) }
      fn pow2bv(x:bitvec<32>) -> bool { bvand(x, bvsub(x, int_to_bv32(1))) == int_to_bv32(0) }
  )]

#[path = "../../lib/rbitvec.rs"]
mod rbitvec;
use rbitvec::UsizeBv;

#[flux::sig(fn (index: usize, size:usize{1 <= size && pow2(size)}) -> usize{v: v < size})]
pub fn wrap_index(index: usize, size: usize) -> usize {
    UsizeBv::from_bv(UsizeBv::to_bv(index) & (UsizeBv::to_bv(size) - UsizeBv::to_bv(1)))
}
