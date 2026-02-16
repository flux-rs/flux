#[flux::assoc(fn foo_no_panic() -> bool)]
trait MyTrait {
    #[flux::sig(fn foo(&Self) -> i32)]
    #[flux::no_panic_if(Self::foo_no_panic())]
    fn foo(&self) -> i32;
}

struct MyStruct;

#[flux::assoc(fn foo_no_panic() -> bool { false })]
impl MyTrait for MyStruct {
    #[flux::sig(fn foo(&Self) -> i32)]
    #[flux::no_panic_if(Self::foo_no_panic())]
    fn foo(&self) -> i32 {
        panic!("oops")
    }
}

#[flux::sig(fn bar(x: &M) -> i32)]
#[flux::no_panic_if(M::foo_no_panic())]
fn bar<M>(my_impl: &M) -> i32
where
    M: MyTrait,
{
    // calling `foo` generically is ok, because the no_panic condition is `M::foo_no_panic()`.
    my_impl.foo();
    let s = MyStruct;
    // `MyStruct::foo` may panic, because the no_panic condition is `MyStruct::foo_no_panic()`, which is false.
    s.foo() //~ ERROR: may panic
}
