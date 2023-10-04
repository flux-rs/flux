#[flux::opaque]
#[flux::refined_by(a: int, b: int)]
pub struct Range {
    a: i32,
    b: i32,
}

impl Range {
    #[flux::trusted]
    #[flux::sig(fn(a: i32, b: i32{b >= a}) -> Range[a, b])]
    pub fn new(a: i32, b: i32) -> Range {
        Range { a, b }
    }

    #[flux::trusted]
    #[flux::sig(fn(&Range[@r]) -> i32[r.a])]
    pub fn fst(&self) -> i32 {
        self.a
    }

    #[flux::trusted]
    #[flux::sig(fn(&Range[@r]) -> i32[r.b])]
    pub fn snd(&self) -> i32 {
        self.b
    }
}

#[flux::sig(fn(Range) -> bool[true])]
fn test(r: Range) -> bool {
    r.snd() - r.fst() >= 0 //~ ERROR refinement type
}
