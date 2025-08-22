#[flux::refined_by(a: int, b: int)]
#[flux::invariant(a > 0)]
#[flux::invariant(b > 0)]
pub struct S {
    #[flux::field({i32[a] | a > 0})]
    fst: i32,
    #[flux::field({i32[b] | a >= b})]
    snd: i32,
}

fn foo(x: i32) -> S {
    let fst = if x > 100 { x } else { 100 };
    let snd = x;
    S { fst, snd } //~ ERROR refinement type
}
