#[flux::refined_by(lo: int, hi: int)]
pub struct Rng {
    #[flux::field(i32[@lo])]
    _lo: i32,
    #[flux::field(i32[@hi])]
    hi: i32,
    #[flux::field(i32{v:lo <= v && v <= hi})]
    cur: i32,
}

impl Rng {
    #[flux::sig(fn(lo:i32, hi:i32{lo <= hi}) -> Rng[lo, hi])]
    pub fn new(lo: i32, hi: i32) -> Self {
        Self { _lo: lo, hi, cur: lo }
    }
}

impl Iterator for Rng {
    type Item = i32;

    #[flux::sig(fn(self: &mut Rng[@lo, @hi]) -> Option<i32{v:lo <= v && v < hi}>)]
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
