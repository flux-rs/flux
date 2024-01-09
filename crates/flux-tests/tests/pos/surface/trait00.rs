pub trait Trait {
    type A;

    fn f(&self) -> <Self as Trait>::A;
}

impl Trait for i32 {
    type A = i32;

    fn f(&self) -> <Self as Trait>::A {
        *self
    }
}

pub fn test00(x: &i32) -> <i32 as Trait>::A {
    x.f()
}

pub fn test01<T: Trait>(x: T) -> <T as Trait>::A {
    x.f()
}
