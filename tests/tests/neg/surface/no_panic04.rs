#[flux::assoc(fn foo_no_panic() -> bool)]
trait MyTrait {
    #[flux::sig(fn foo(&Self) -> i32)]
    #[flux::no_panic_if(Self::foo_no_panic())]
    fn foo(&self) -> i32;
}

struct MyStruct;

#[flux::assoc(fn foo_no_panic() -> bool { true })]
impl MyTrait for MyStruct {
    #[flux::sig(fn foo(&Self) -> i32)]
    fn foo(&self) -> i32 {
        3
    }
}

#[flux::sig(fn bar(x: &M) -> i32)]
#[flux::no_panic_if(M::foo_no_panic())]
fn bar<M>(my_impl: &M) -> i32
where
    M: MyTrait,
{
    // should be ok. the sig of `foo` implies that `foo_no_panic` is true, so the no-panic condition is satisfied.
    my_impl.foo();
    // is not ok, because MyStruct::foo's no_panic is `false`.
    let s = MyStruct;
    s.foo() //~ ERROR: may panic
}
