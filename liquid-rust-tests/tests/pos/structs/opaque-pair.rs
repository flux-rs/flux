#![feature(register_tool)]
#![register_tool(lr)]

#[lr::refined_by(a: int, b: int)]
pub struct Pair {
    a: i32,
    b: i32,
}

impl Pair {
    #[lr::assume]
    #[lr::ty(fn<a: int, b: int>(&Pair @ {a, b}) -> i32@a)]
    fn fst(&self) -> i32 {
        self.a
    }

    #[lr::assume]
    #[lr::ty(fn<a: int, b: int>(&Pair @ {a, b}) -> i32@b)]
    fn snd(&self) -> i32 {
        self.a
    }
}

#[lr::ty(fn(bool @ true) -> i32@0)]
pub fn assert(b: bool) -> i32 {
    0
}

#[lr::ty(fn<a: int, b: int{b >= a}>(Pair @ {a, b}) -> i32@0)]
pub fn foo(p: Pair) -> i32 {
    let fst = p.fst();
    let snd = p.snd();
    assert(snd - fst >= 0);
    0
}
