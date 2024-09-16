pub trait MyTrait<'a> {}
pub struct MyStruct {
    t: &'static dyn MyTrait<'static>,
}

pub fn new(t: &'static dyn MyTrait) -> MyStruct {
    MyStruct { t }
}
