#![allow(dead_code)]

// Define a new type to wrap `u32` but indexed by actual bitvec
#[flux::opaque]
#[flux::refined_by(value: bitvec<32>)]
pub struct Bv32(u32);

impl Bv32 {
    // Define "cast" functions
    #[flux::trusted]
    #[flux::sig(fn (n:u32) -> Bv32[int_to_bv32(n)])]
    pub fn to_bv(n: u32) -> Bv32 {
        Bv32(n)
    }

    #[flux::trusted]
    #[flux::sig(fn (bv:Bv32) -> u32[bv32_to_int(bv)])]
    pub fn from_bv(bv: Bv32) -> u32 {
        bv.0
    }
}

impl std::ops::Sub<Bv32> for Bv32 {
    type Output = Bv32;
    #[flux::trusted]
    #[flux::sig(fn (x:Bv32, y:Bv32) -> Bv32[bvsub(x,y)])]
    fn sub(self, other: Bv32) -> Bv32 {
        Bv32(self.0 - other.0)
    }
}

impl std::ops::BitAnd<Bv32> for Bv32 {
    type Output = Bv32;
    #[flux::trusted]
    #[flux::sig(fn (x:Bv32, y:Bv32) -> Bv32[bvand(x,y)])]
    fn bitand(self, other: Bv32) -> Bv32 {
        Bv32(self.0 & other.0)
    }
}
