#[flux::refined_by(x: int, y: int)]
pub struct X {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

#[flux::sig(fn (x: X[@old_x]) -> X[{ y: 2, x: 1 }])]
fn f(mut x: X) -> X {
    x.x = 1;
    x.y = 2;
    x
}
