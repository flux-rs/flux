#[flux::refined_by(val: real)]
#[flux::opaque]
pub struct Num(f32);

#[flux::trusted]
impl Num {
    #[flux::sig(fn() -> Num[2.0f32])] //~ ERROR invalid suffix `f32` for number literal
    pub fn two() -> Self {
        Num(2.0)
    }
}
