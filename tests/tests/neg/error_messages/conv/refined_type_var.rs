struct S<T> {
    #[flux::field(T{v: v > 0})] //~ ERROR type cannot be refined
    x: T,
}

enum E<T> {
    #[flux::variant((T[@n, @m]) -> E<T>)] //~ ERROR type cannot be refined
    A(T),
}

pub trait MyTrait {
    fn foo(&self) -> Self;
}

#[flux::sig(fn[hrn q: T -> bool](&T{v:q(v)}) -> T{v: q(v)})]
//~^ ERROR type cannot be refined
pub fn baz<T: MyTrait>(x: &T) -> T {
    x.foo()
}

// This error is confusing, but it should go once we make all types refinable
#[flux::sig(fn(x: T) -> i32[x])] //~ ERROR type cannot be refined
fn generic<T>(x: T) -> i32 {
    0
}
