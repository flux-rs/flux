use core::{
    cmp::Ordering,
    ops::{Add, BitAnd, BitOr, Not, Rem, Shl, Shr, Sub},
};

use flux_attrs::*;

#[derive(Debug, Clone, Copy, Hash)]
#[opaque]
#[refined_by(x: bitvec<32>)]
pub struct BV32(u32);

#[trusted]
impl PartialOrd for BV32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }

    #[sig(fn(&BV32[@x], &BV32[@y]) -> bool[bv_ule(x, y)])]
    fn le(&self, other: &Self) -> bool {
        self.0 <= other.0
    }

    #[sig(fn(&BV32[@x], &BV32[@y]) -> bool[bv_ult(x, y)])]
    fn lt(&self, other: &Self) -> bool {
        self.0 < other.0
    }

    #[sig(fn(&BV32[@x], &BV32[@y]) -> bool[bv_uge(x, y)])]
    fn ge(&self, other: &Self) -> bool {
        self.0 >= other.0
    }

    #[sig(fn(&BV32[@x], &BV32[@y]) -> bool[bv_ugt(x, y)])]
    fn gt(&self, other: &Self) -> bool {
        self.0 > other.0
    }
}

#[trusted]
impl BV32 {
    #[sig(fn (u32[@val]) -> BV32[bv_int_to_bv32(val)])]
    pub const fn new(value: u32) -> BV32 {
        BV32(value)
    }

    #[sig(fn(BV32[@x], BV32[@y]) -> BV32[bv_add(x, y)])]
    pub fn wrapping_add(self, other: BV32) -> BV32 {
        BV32(self.0.wrapping_add(other.0))
    }
}

impl From<u32> for BV32 {
    #[trusted]
    #[sig(fn(u32[@val]) -> BV32[bv_int_to_bv32(val)])]
    fn from(value: u32) -> BV32 {
        BV32(value)
    }
}

impl Into<u32> for BV32 {
    #[trusted]
    #[sig(fn(BV32[@val]) -> u32[bv_bv32_to_int(val)])]
    fn into(self) -> u32 {
        self.0
    }
}

impl Not for BV32 {
    type Output = BV32;

    #[trusted]
    #[sig(fn(BV32[@x]) -> BV32[bv_not(x)])]
    fn not(self) -> BV32 {
        BV32(!self.0)
    }
}

impl BitAnd for BV32 {
    type Output = BV32;

    #[trusted]
    #[sig(fn(BV32[@x], BV32[@y]) -> BV32[bv_and(x, y)])]
    fn bitand(self, rhs: Self) -> BV32 {
        BV32(self.0 & rhs.0)
    }
}

impl BitOr for BV32 {
    type Output = BV32;

    #[trusted]
    #[sig(fn(BV32[@x], BV32[@y]) -> BV32[bv_or(x, y)])]
    fn bitor(self, rhs: Self) -> BV32 {
        BV32(self.0 | rhs.0)
    }
}

impl Shl for BV32 {
    type Output = BV32;

    #[trusted]
    #[sig(fn(BV32[@x], BV32[@y]) -> BV32[bv_shl(x, y)])]
    fn shl(self, rhs: Self) -> BV32 {
        BV32(self.0 << rhs.0)
    }
}

impl Shr for BV32 {
    type Output = BV32;

    #[trusted]
    #[sig(fn(BV32[@x], BV32[@y]) -> BV32[bv_lshr(x, y)])]
    fn shr(self, rhs: Self) -> BV32 {
        BV32(self.0 >> rhs.0)
    }
}

impl Add for BV32 {
    type Output = BV32;

    #[trusted]
    #[sig(fn(BV32[@val1], BV32[@val2]) -> BV32[bv_add(val1, val2)])]
    fn add(self, rhs: Self) -> BV32 {
        BV32(self.0 + rhs.0)
    }
}

impl Sub for BV32 {
    type Output = BV32;

    #[trusted]
    #[sig(fn(BV32[@val1], BV32[@val2]) -> BV32[bv_sub(val1, val2)])]
    fn sub(self, rhs: Self) -> BV32 {
        BV32(self.0.wrapping_add(!rhs.0))
    }
}

impl Rem for BV32 {
    type Output = BV32;

    #[trusted]
    #[sig(fn(BV32[@val1], BV32[@val2]) -> BV32[bv_urem(val1, val2)])]
    fn rem(self, rhs: Self) -> BV32 {
        BV32(self.0 & rhs.0)
    }
}

#[trusted]
impl PartialEq for BV32 {
    #[sig(fn(&BV32[@val1], &BV32[@val2]) -> bool[val1 == val2])]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    #[sig(fn(&BV32[@val1], &BV32[@val2]) -> bool[val1 != val2])]
    fn ne(&self, other: &Self) -> bool {
        self.0 != other.0
    }
}

impl Eq for BV32 {}
