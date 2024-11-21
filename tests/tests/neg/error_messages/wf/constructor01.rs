#[flux::refined_by(x: int, y: int)]
pub struct X {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

// z is not a valid field for X
#[flux::sig(fn (x: X[@old_x]) -> X[X { y: 2, x: 1, z: 3 }])] //~ ERROR no field `z` on sort `X`
fn f1(mut x: X) -> X {
    x.x = 1;
    x.y = 2;
    x
}

// z is not a valid field for X
#[flux::sig(fn (x: X[@old_x]) -> X[{ y: 2, x: 1, z: 3 }])] //~ ERROR no field `z` on sort `X`
fn f2(mut x: X) -> X {
    x.x = 1;
    x.y = 2;
    x
}
