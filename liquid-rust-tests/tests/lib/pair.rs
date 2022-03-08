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
    #[lr::ty(fn<a1: int, a2: int, b: int>(
        self: Pair @ {a1, b};
        ref<self>,
        i32@a2
    ) -> i32@0;
        self: Pair @ {a2, b}
    )]
    pub fn set_fst(&mut self, a: i32) -> i32 {
        self.a = a;
        0
    }

    #[lr::assume]
    #[lr::ty(fn<a: int, b: int>(&Pair @ {a, b}) -> i32@b)]
    pub fn snd(&self) -> i32 {
        self.b
    }

    #[lr::assume]
    #[lr::ty(fn<a: int, b1: int, b2: int>(
        self: Pair @ {a, b1};
        ref<self>,
        i32@b2
    ) -> i32@0;
        self: Pair @ {a, b2}
    )]
    pub fn set_snd(&mut self, b: i32) -> i32 {
        self.b = b;
        0
    }
}
