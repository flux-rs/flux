#[flux::opaque]
#[flux::refined_by(init: bool)]
pub union MyUnion {
    pub val: u8,
    pub uninit: (),
}

#[flux::trusted]
#[flux::sig(fn() -> MyUnion[false])]
pub fn uninit() -> MyUnion {
    MyUnion { uninit: () }
}
