#[flux::assoc(fn f1() -> bool)]
trait Baz {
    #[flux::spec(fn (s: Self) -> bool[<Self as Baz>::f1()])]
    fn into_bool(self) -> bool;
}

#[flux::final_assoc(fn f2() -> bool { <T as Baz>::f1() })]
trait Foo<T: Baz> {}

struct Bar<T: Baz, F: Foo<T>> {
    inner1: F,
    inner2: T,
}

impl<T: Baz, F: Foo<T>> Bar<T, F> {
    #[flux::spec(fn (s: Self) -> bool[<Self as Foo<T>>::f2()])]
    pub fn foo_bar_baz(self) -> bool {
        self.inner2.into_bool()
    }
}
