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

    #[flux::sig(fn(x: &Num[@xx], y: &Num[@yy]) -> Num[xx * yy])]
    pub fn mult(&self, other: &Num) -> Num {
        Num(self.0 * other.0)
    }
}

#[flux::sig(fn(x: &Num[@xx], y: &Num[@yy], z: &Num[@zz]) -> Num[xx + yy + zz])]
pub fn add3(x: &Num, y: &Num, z: &Num) -> Num {
    x.add(&y).add(&z)
}

#[flux::sig(fn(x: &Num[@xx]) -> Num[2.0 * xx])]
pub fn add_mult_test(x: &Num) -> Num {
    x.add(x)
}

#[flux::sig(fn(x: &Num[@xx], y: &Num[@yy]) -> Num[xx])]
pub fn add_sub_test(x: &Num, y: &Num) -> Num {
    x.add(y).subtract(y)
}
