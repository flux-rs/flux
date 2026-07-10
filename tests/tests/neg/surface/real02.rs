#[flux::refined_by(val: real)]
#[flux::opaque]
pub struct Num(f32);

#[flux::trusted]
impl Num {
    #[flux::sig(fn(x: &Num[@xx], y: &Num[@yy]) -> Num[xx + yy])]
    pub fn add(&self, other: &Num) -> Num {
        Num(self.0 + other.0)
    }

    #[flux::sig(fn(x: &Num[@xx], y: &Num[@yy]) -> Num[xx - yy])]
    pub fn subtract(&self, other: &Num) -> Num {
        Num(self.0 - other.0)
    }
}

// wrong: claims x + y = x (only true when y = 0)
#[flux::sig(fn(x: &Num[@xx], y: &Num[@yy]) -> Num[xx])]
pub fn wrong_add(x: &Num, y: &Num) -> Num {
    x.add(y) //~ ERROR refinement type error
}

// wrong: claims (x + y) - y = x + 1.0
#[flux::sig(fn(x: &Num[@xx], y: &Num[@yy]) -> Num[xx + 1.0])]
pub fn wrong_add_sub(x: &Num, y: &Num) -> Num {
    x.add(y).subtract(y) //~ ERROR refinement type error
}
