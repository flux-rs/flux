#[flux::assoc(fn foo_no_panic() -> bool)]
trait MyTrait {
    #[flux::sig(fn(Self) -> i32)]
    fn foo(&self) -> i32;
}

struct MyStruct;

#[flux::assoc(fn foo_no_panic() -> bool { false })]
impl MyTrait for MyStruct {
    #[flux::sig(fn(Self) -> i32)]
    fn foo(&self) -> i32 {
        panic!("oh no!");
    }
}

#[flux::sig(fn(x: &MyTrait) -> i32)]
#[flux::no_panic_if(MyTrait::foo_no_panic())]
fn bar(my_impl: &dyn MyTrait) -> i32 {
    my_impl.foo() //~ ERROR: refinement
}
