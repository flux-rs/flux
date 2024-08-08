// https://github.com/flux-rs/flux/issues/686

#[allow(dead_code)]
#[flux::sig(fn(x: bool[true]))]
pub fn assert(_x: bool) {}

#[flux::opaque]
#[flux::refined_by(v: bitvec<32>)]
struct Register {
    inner: u32,
}

impl Register {
    #[flux::sig(fn(u32[@n]) -> Register[bv_int_to_bv32(n)])]
    #[flux::trusted]
    fn new(v: u32) -> Self {
        Register { inner: v }
    }

    #[flux::sig(fn(&Register[@n]) -> u64[bv_bv64_to_int(bv_zero_extend_32_to_64(n))])]
    #[flux::trusted]
    fn zero_extend(&self) -> u64 {
        self.inner as u64
    }

    #[flux::sig(fn(&Register[@n]) -> u64[bv_bv64_to_int(bv_sign_extend_32_to_64(n))])]
    #[flux::trusted]
    fn sign_extend(&self) -> u64 {
        self.inner as i32 as i64 as u64
    }
}

pub fn test_bv_extensions() {
    let r = Register::new(u32::MAX);
    assert(r.zero_extend() == u32::MAX as u64);
    assert(r.zero_extend() == 12); //~ ERROR refinement type
    assert(r.sign_extend() == u64::MAX);
    assert(r.sign_extend() == 12); //~ ERROR refinement type
}
