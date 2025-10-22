use flux_rs::{
    attrs::*,
    bitvec::{BV8, BV32},
};

#[spec(fn (x:BV8[1]) -> BV8[8])]
pub fn test_shl_8(x: BV8) -> BV8 {
    x << 3
}

#[spec(fn (x:BV32[1]) -> BV32[8])]
pub fn test_shl_32(x: BV32) -> BV32 {
    x << 3
}

#[spec(fn (x:BV8[8]) -> BV8[1])]
pub fn test_shr_8(x: BV8) -> BV8 {
    x >> 3
}

#[spec(fn (x:BV32[8]) -> BV32[1])]
pub fn test_shr_32(x: BV32) -> BV32 {
    x >> 3
}

#[spec(fn (x:BV8[4]) -> BV8[5])]
pub fn test_or_8(x: BV8) -> BV8 {
    x | 1
}

#[spec(fn (x:BV32[4]) -> BV32[5])]
pub fn test_or_32(x: BV32) -> BV32 {
    x | 1
}

#[sig(fn (x:BV8[6]) -> BV8[2])]
pub fn test_and_8(x: BV8) -> BV8 {
    x & 3
}

#[sig(fn (x:BV32[6]) -> BV32[2])]
pub fn test_and_32(x: BV32) -> BV32 {
    x & 3
}
