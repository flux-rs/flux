#[flux::refined_by(lo: int, hi: int)]
pub struct RngIter {
    #[flux::field(i32[lo])]
    _lo: i32,
    #[flux::field(i32[hi])]
    hi: i32,
    #[flux::field(i32{v:lo <= v && v <= hi})]
    cur: i32,
}

impl RngIter {
    #[flux::sig(fn(lo: i32, hi: i32{lo <= hi}) -> RngIter[lo, hi])]
    pub fn new(lo: i32, hi: i32) -> RngIter {
        Self { _lo: lo, hi, cur: lo }
    }
}

#[flux::refined_by(lo: int, hi: int)]
pub struct Rng {
    #[flux::field(i32[lo])]
    lo: i32,
    #[flux::field({i32[hi] | lo <= hi})]
    hi: i32,
}

impl Rng {
    #[flux::sig(fn(lo:i32, hi:i32{lo <= hi}) -> Rng[lo, hi])]
    pub fn new(lo: i32, hi: i32) -> Rng {
        Self { lo, hi }
    }
}

impl Iterator for RngIter {
    type Item = i32;

    #[flux::sig(fn(self: &mut RngIter[@lo, @hi]) -> Option<i32{v: lo <= v && v < hi}>)]
    fn next(&mut self) -> Option<i32> {
        let cur = self.cur;
        let hi = self.hi;
        if cur < hi {
            self.cur = cur + 1;
            Some(cur)
        } else {
            None
        }
    }
}

impl IntoIterator for Rng {
    type Item = i32;
    type IntoIter = RngIter;

    #[flux::sig(fn(Rng[@lo, @hi]) -> RngIter[lo, hi])]
    fn into_iter(self) -> RngIter {
        RngIter::new(self.lo, self.hi)
    }
}
