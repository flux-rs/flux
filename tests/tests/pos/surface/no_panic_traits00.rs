trait MyTrait {
    fn do_something(&self) -> i32;
}

struct MyStruct {}

impl MyTrait for MyStruct {
    #[flux::no_panic]
    fn do_something(&self) -> i32 {
        42
    }
}

#[flux::no_panic]
#[flux::sig(fn(f: T) -> i32 requires T::no_panic())]
fn bar<T: MyTrait>(f: T) -> i32 {
    f.do_something()
}

#[flux::no_panic]
fn foo() {
    bar(MyStruct {});
}
