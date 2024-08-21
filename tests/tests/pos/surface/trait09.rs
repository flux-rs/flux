pub trait Mickey {
    type Output;
    fn add(&self, other: &Self) -> Self::Output;
}

pub trait Mouse: Mickey<Output = Self> {}

pub fn foo<F: Mouse>(x: F, y: F) -> F {
    x.add(&y)
}
