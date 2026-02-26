#[flux::assoc(fn blueberry_no_panic() -> bool)]
pub trait MyTrait<'a> {
    #[flux::sig(fn(&Self) -> ())]
    #[flux::no_panic_if(Self::blueberry_no_panic())]
    fn blueberry(&self) {
        let x = 3;
    }
}

pub struct MyStruct<'a> {
    field: &'a dyn MyTrait<'a>,
}

#[flux::no_panic_if(MyTrait::blueberry_no_panic())]
fn foo(s: &MyStruct) {
    s.field.blueberry();
}
