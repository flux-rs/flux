#[flux::refined_by(b: bool, y: int)]
pub struct S {
    #[flux::field(bool[b])]
    b: bool,
    #[flux::field(u32[y])]
    y: u32,
}

#[flux::sig(fn (S[@old_s]) -> S[S { y: 2, b: true }])]
fn f(mut s: S) -> S {
    s.b = true;
    s.y = 2;
    s
}
