#[flux::refined_by(a: int, b: int)]
pub struct Pair {
    #[flux::field(i32[a])]
    left: i32,
    #[flux::field(i32[b])]
    right: i32,
}

#[flux::sig(fn(p: Pair, b: bool) -> i32[p.a])]
fn test00(mut p: Pair, b: bool) -> i32 {
    if b {
        // this is a function call so the `Pair` remains folded
        add_right(&mut p, 1);
    }
    p.left
}

#[flux::sig(fn(p: Pair) -> i32[p.a])]
fn test01(mut p: Pair) -> i32 {
    let mut i = 0;
    while i < 10 {
        // this is a function call so the `Pair` remains folded
        add_right(&mut p, 1);
        i += 1;
    }
    p.left
}

#[flux::sig(fn(p: &strg Pair[@a, @b], n: i32) ensures p: Pair[a, b + n])]
fn add_right(p: &mut Pair, n: i32) {
    p.right += n;
}
