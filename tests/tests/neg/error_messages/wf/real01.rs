#[flux::refined_by(val: real)]
#[flux::opaque]
pub struct Num(f32);

#[flux::trusted]
impl Num {
    #[flux::sig(fn() -> Num[2])] //~ ERROR `2` is not of sort `real`
    pub fn two() -> Self {
        Num(2.0)
    }
}
