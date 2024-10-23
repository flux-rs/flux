pub trait MyTrait {
    type A;

    fn f(&self) -> <Self as MyTrait>::A;
}

impl MyTrait for i32 {
    type A = i32;

    fn f(&self) -> <Self as MyTrait>::A {
        *self
    }
}

pub fn test00(x: &i32) -> <i32 as MyTrait>::A {
    x.f()
}

pub fn test01<T: MyTrait>(x: T) -> <T as MyTrait>::A {
    x.f()
}
