#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int, b: int, p: (int, int) -> bool)]
struct Pair {
    #[flux::field(i32[@a])]
    fst: i32,
    #[flux::field({i32[@b] : p(a, b)})]
    snd: i32,
}

#[flux::sig(fn() -> Pair)]
fn test00() -> Pair {
    Pair { fst: 0, snd: 1 }
}

#[flux::sig(fn(Pair[@a, @b, |a, b| a < b]) -> i32{v: v > 0})]
fn test01(pair: Pair) -> i32 {
    pair.snd - pair.fst
}

fn test02() {
    let pair = Pair { fst: 0, snd: 1 };
    let x = test01(pair);
}

#[flux::sig(fn(x: i32, Pair[@a, @b, |a, b| a > x]) -> i32{v: v > x})]
fn test03(x: i32, pair: Pair) -> i32 {
    pair.fst
}
