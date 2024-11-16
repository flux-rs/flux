#[flux::refined_by(x: int, y: int)]
pub struct X {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

// z is not a valid field for X
#[flux::sig(fn (x: X[@old_x]) -> X[X { y: 2, x: 1, z: 3 }])] //~ ERROR invalid field referenced in constructor
fn f1(mut x: X) -> X {
    x.x = 1;
    x.y = 2;
    x
}
