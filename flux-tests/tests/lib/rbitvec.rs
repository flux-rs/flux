#![allow(dead_code)]

// Define a new type to wrap `usize` but indexed by actual bitvec
#[flux::refined_by(value: bitvec<32>)]
pub struct UsizeBv {
    inner: usize,
}

impl UsizeBv {
    // Define "cast" functions
    #[flux::trusted]
    #[flux::sig(fn (n:usize) -> UsizeBv[int_to_bv32(n)])]
    pub fn to_bv(inner: usize) -> UsizeBv {
        UsizeBv { inner }
    }

    #[flux::trusted]
    #[flux::sig(fn (bv:UsizeBv) -> usize[bv32_to_int(bv)])]
    pub fn from_bv(bv: UsizeBv) -> usize {
        bv.inner
    }
}

impl std::ops::Sub<UsizeBv> for UsizeBv {
    type Output = UsizeBv;
    #[flux::trusted]
    #[flux::sig(fn (x:UsizeBv, y:UsizeBv) -> UsizeBv[bvsub(x,y)])]
    fn sub(self, other: UsizeBv) -> UsizeBv {
        UsizeBv { inner: self.inner - other.inner }
    }
}

impl std::ops::BitAnd<UsizeBv> for UsizeBv {
    type Output = UsizeBv;
    #[flux::trusted]
    #[flux::sig(fn (x:UsizeBv, y:UsizeBv) -> UsizeBv[bvand(x,y)])]
    fn bitand(self, other: UsizeBv) -> UsizeBv {
        UsizeBv { inner: self.inner & other.inner }
    }
}
