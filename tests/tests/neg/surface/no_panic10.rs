#[flux_rs::assoc(fn foo_no_panic() -> bool)]
trait MyTrait {
    #[flux_rs::sig(fn(&Self) -> bool)]
    #[flux_rs::no_panic_if(Self::foo_no_panic())]
    fn foo(&self) -> bool;
}

#[flux_rs::no_panic_if(true)]
#[flux_rs::sig(fn(_) -> ())]
fn foo1<T: MyTrait>(thing: &T) {
    thing.foo(); //~ ERROR may panic
    let x = || {
        thing.foo(); //~ ERROR may panic
    };
}

#[flux_rs::no_panic_if(T::foo_no_panic())]
#[flux_rs::sig(fn(_) -> ())]
fn foo2<T: MyTrait>(thing: &T) {
    thing.foo(); // this is a-ok
    let x = || {
        thing.foo(); // and this is a-ok too!
    };
}
