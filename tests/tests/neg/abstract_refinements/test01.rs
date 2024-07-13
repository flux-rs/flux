#[flux::refined_by(a: int, b: int, hrn p: (int, int) -> bool)]
struct Pair {
    #[flux::field(i32[a])]
    fst: i32,
    #[flux::field({i32[b] | p(a, b)})]
    snd: i32,
}

#[flux::sig(fn(Pair[@a, @b, |a, b| a <= b]) -> i32{v: v > 0})]
fn test00(pair: Pair) -> i32 {
    pair.snd - pair.fst //~ ERROR refinement type
}

fn test01() {
    let pair = Pair { fst: 1, snd: 0 };
    let x = test00(pair); //~ ERROR refinement type
}

#[flux::sig(fn(x: i32, Pair[@a, @b, |a, b| a >= x]) -> i32{v: v > x})]
fn test02(x: i32, pair: Pair) -> i32 {
    pair.fst //~ ERROR refinement type
}

fn test03() {
    let pair = Pair { fst: 0, snd: 0 };
    test02(10, pair); //~ ERROR refinement type
}
