pub trait MyTrait {
    fn foo() -> i32;
}

pub trait OtherTrait {
    fn foo() -> i32;
}

impl<T> MyTrait for Vec<T> {
    fn foo() -> i32 {
        10
    }
}
impl<T> OtherTrait for Vec<T> {
    fn foo() -> i32 {
        10
    }
}
