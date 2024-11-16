#![allow(unused)]

#[flux::refined_by(x: int, y: int)]
pub struct X {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

#[flux::refined_by(x: X)]
pub struct Y {
    #[flux::field(X[x])]
    big_x: X,
}

#[flux::sig(fn (x: X[@old_x]) -> X[X { y: 2, x: 1 }])]
fn f(mut x: X) -> X {
    x.x = 1;
    x.y = 2;
    x
}

#[flux::sig(fn (x: Y[@old_y]) -> Y[Y { x: X { x: 1, y: 1 } }])]
fn f_through_y(mut y: Y) -> Y {
    y.big_x.x = 1;
    y.big_x.y = 2;
    y //~ ERROR refinement type error
}
