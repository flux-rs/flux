use flux_rs::{attrs::*, bitvec::BV32};

#[sig(fn(x: BV32) -> BV32[x + 1])]
pub fn test_02(x: BV32) -> BV32 {
    x + BV32::new(2) //~ ERROR refinement type
}

#[sig(fn() -> BV32[5])]
pub fn test_05() -> BV32 {
    BV32::new(0x6) //~ ERROR refinement type
}

#[sig(fn(x: BV32, y:BV32) -> bool[x + y > 5])]
pub fn test_06(x: BV32, y: BV32) -> bool {
    x > y //~ ERROR refinement type
}

#[sig(fn(x: BV32, y:BV32) -> bool[x + y > 0])]
pub fn test_07(x: BV32, y: BV32) -> bool {
    x + y > x - y //~ ERROR refinement type
}

#[sig(fn() -> BV32[5])]
pub fn test_08() -> BV32 {
    BV32::new(0x50) //~ ERROR refinement type
}
