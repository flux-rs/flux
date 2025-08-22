use std::ops::{Add, Sub};

#[flux::opaque]
#[flux::refined_by(x: bitvec<32>)]
pub struct BV32(u32);

impl BV32 {
    #[flux::trusted]
    #[flux::sig(fn (u32[@x]) -> BV32[bv_int_to_bv32(x)])]
    pub fn new(x: u32) -> Self {
        BV32(x)
    }
}

impl Add for BV32 {
    type Output = BV32;

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (BV32[@val1], BV32[@val2]) -> BV32[bv_add(val1, val2)])]
    fn add(self, rhs: Self) -> BV32 {
        BV32(self.0 + rhs.0)
    }
}

impl Sub for BV32 {
    type Output = BV32;

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (BV32[@val1], BV32[@val2]) -> BV32[bv_sub(val1, val2)])]
    fn sub(self, rhs: Self) -> BV32 {
        BV32(self.0.wrapping_add(!rhs.0))
    }
}

impl PartialEq for BV32 {
    #[flux::trusted]
    #[flux::sig(fn (&BV32[@val1], &BV32[@val2]) -> bool[val1 == val2])]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    #[flux::trusted]
    #[flux::sig(fn (&BV32[@val1], &BV32[@val2]) -> bool[val1 != val2])]
    fn ne(&self, other: &Self) -> bool {
        self.0 != other.0
    }
}

impl PartialOrd for BV32 {
    #[flux::trusted]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }

    #[flux::trusted]
    #[flux::sig(fn (&BV32[@x], &BV32[@y]) -> bool[bv_ule(x, y)])]
    fn le(&self, other: &Self) -> bool {
        self.0 <= other.0
    }

    #[flux::trusted]
    #[flux::sig(fn (&BV32[@x], &BV32[@y]) -> bool[bv_ult(x, y)])]
    fn lt(&self, other: &Self) -> bool {
        self.0 < other.0
    }

    #[flux::trusted]
    #[flux::sig(fn (&BV32[@x], &BV32[@y]) -> bool[bv_uge(x, y)])]
    fn ge(&self, other: &Self) -> bool {
        self.0 >= other.0
    }

    #[flux::trusted]
    #[flux::sig(fn (&BV32[@x], &BV32[@y]) -> bool[bv_ugt(x, y)])]
    fn gt(&self, other: &Self) -> bool {
        self.0 > other.0
    }
}

#[flux::sig(fn (BV32[@x]) -> bool[bv_ule(x, x)])]
pub fn trivial_le(x: BV32) -> bool {
    x <= x
}

#[flux::sig(fn (BV32[@x]) -> bool[bv_ult(x, x)])]
pub fn trivial_lt(x: BV32) -> bool {
    x < x
}

#[flux::sig(fn (BV32[@x]) -> bool[bv_uge(x, x)])]
pub fn trivial_ge(x: BV32) -> bool {
    x <= x
}

#[flux::sig(fn (BV32[@x]) -> bool[bv_ugt(x, x)])]
pub fn trivial_gt(x: BV32) -> bool {
    x < x
}

#[flux::sig(fn (BV32[@x], BV32[@y]) -> bool[
    bv_ule(x, bv_int_to_bv32(10))
    && 
    bv_uge(y, bv_int_to_bv32(20))
    &&
    bv_ult(x, bv_int_to_bv32(11))
    &&
    bv_ugt(y, bv_int_to_bv32(21))
])]
pub fn real_example(x: BV32, y: BV32) -> bool {
    x <= BV32::new(10) && y >= BV32::new(20) && x < BV32::new(11) && y > BV32::new(21)
}


#[flux_rs::sig(fn (BV32[@x], BV32[@y]) -> bool[true] requires bv_ult(x, y) && bv_ugt(x, bv_int_to_bv32(0x20)) && bv_ult(y, bv_int_to_bv32(0xFF)))]
fn lt_imp(x: BV32, y: BV32) -> bool {
    x - BV32::new(0x20) < y + BV32::new(0x20)
}

#[flux_rs::sig(fn (BV32[@x], BV32[@y]) -> bool[true] requires bv_ule(x, y) && bv_uge(x, bv_int_to_bv32(0x20)) && bv_ule(y, bv_int_to_bv32(0xFF)))]
fn le_imp(x: BV32, y: BV32) -> bool {
    x - BV32::new(0x20) <= y + BV32::new(0x20)
}

#[flux_rs::sig(fn (BV32[@x], BV32[@y]) -> bool[true] requires bv_ugt(x, y) && bv_ugt(y, bv_int_to_bv32(0x20)) && bv_ult(x, bv_int_to_bv32(0xFF)))]
fn gt_imp(x: BV32, y: BV32) -> bool {
    x + BV32::new(0x20) > y - BV32::new(0x20)
}

#[flux_rs::sig(fn (BV32[@x], BV32[@y]) -> bool[true] requires bv_uge(x, y) && bv_uge(y, bv_int_to_bv32(0x20)) && bv_ule(x, bv_int_to_bv32(0xFF)))]
fn ge_imp(x: BV32, y: BV32) -> bool {
    x + BV32::new(0x20) >= y - BV32::new(0x20)
}
