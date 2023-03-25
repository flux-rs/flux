#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs(
      fn pow2(x:int) -> bool { pow2bv(int_to_bv32(x)) }
      fn pow2bv(x:bitvec<32>) -> bool { bvand(x, bvsub(x, int_to_bv32(1))) == int_to_bv32(0) }
  )]

// Define a new type to wrap `usize` but indexed by actual bitvec
#[flux::refined_by(value: bitvec<32>)]
struct UsizeBv {
    inner: usize,
}

// Define "cast" functions
#[flux::trusted]
#[flux::sig(fn (n:usize) -> UsizeBv[int_to_bv32(n)])]
fn to_bv(inner: usize) -> UsizeBv {
    UsizeBv { inner }
}

#[flux::trusted]
#[flux::sig(fn (bv:UsizeBv) -> usize[bv32_to_int(bv)])]
fn from_bv(bv: UsizeBv) -> usize {
    bv.inner
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

#[flux::sig(fn (index: usize, size:usize{1 <= size && pow2(size)}) -> usize{v: v < size})]
pub fn wrap_index(index: usize, size: usize) -> usize {
    from_bv(to_bv(index) & (to_bv(size) - to_bv(1)))
}
