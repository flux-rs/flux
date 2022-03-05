#[lr::opaque]
#[lr::refined_by(a: int, b: int)]
pub struct Pair {
    a: i32,
    b: i32,
}

impl Pair {
    #[lr::assume]
    #[lr::ty(fn<a: int, b: int>(i32 @ a, i32 @ b) -> Pair @ {a, b})]
    pub fn new(a: i32, b: i32) -> Pair {
        Pair { a, b }
    }

    #[lr::assume]
    #[lr::ty(fn<a: int, b: int>(&Pair @ {a, b}) -> i32@a)]
    pub fn fst(&self) -> i32 {
        self.a
    }

    #[lr::assume]
    #[lr::ty(fn<a: int, b: int>(&Pair @ {a, b}) -> i32@b)]
    pub fn snd(&self) -> i32 {
        self.a
    }
}
