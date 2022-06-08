#[lr::opaque]
#[lr::refined_by(a: int, b: int)]
pub struct Pair {
    a: i32,
    b: i32,
}

impl Pair {
    #[lr::assume]
    #[lr::sig(fn(a: i32, b: i32) -> Pair[a, b])]
    pub fn new(a: i32, b: i32) -> Pair {
        Pair { a, b }
    }

    #[lr::assume]
    #[lr::sig(fn(&Pair[@a, @b]) -> i32[a])]
    pub fn fst(&self) -> i32 {
        self.a
    }

    #[lr::assume]
    #[lr::sig(
    fn(self: &strg Pair[@a1, @b], i32[@a2]) -> i32[0]
    ensures self: Pair[a2, b]
    )]
    pub fn set_fst(&mut self, a: i32) -> i32 {
        self.a = a;
        0
    }

    #[lr::assume]
    #[lr::sig(fn(&Pair[@a, @b]) -> i32[b])]
    pub fn snd(&self) -> i32 {
        self.b
    }

    #[lr::assume]
    #[lr::sig(
    fn(self: &strg Pair[@a, @b1], i32[@b2]) -> i32[0]
    ensures self: Pair[a, b2]
    )]
    pub fn set_snd(&mut self, b: i32) -> i32 {
        self.b = b;
        0
    }
}
