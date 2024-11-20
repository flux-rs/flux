#[flux::refined_by(x: int, y: int)]
struct S1 {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

#[flux::refined_by(x: int, y: int)]
struct S2 {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

#[flux::sig(fn (S1[@s1]) -> S1[S2 { x: 1, y: 2 }])] //~ERROR mismatched sorts
fn foo(mut s1: S1) -> S1 {
    s1.x = 1;
    s1.y = 2;
    s1
}
