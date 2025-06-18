#[flux::assoc(fn f1() -> bool)]
#[flux::assoc(final fn f2() -> bool { <Self as Foo>::f1() })]
trait Foo {
    #[flux::spec(fn () -> bool[<Self as Foo>::f1()])]
    fn get_bool() -> bool;
}

struct Bar<F: Foo> {
    inner: F,
}

impl<F: Foo> Bar<F> {
    #[flux::spec(fn () -> bool[<F as Foo>::f1()])]
    fn implies() -> bool {
        F::get_bool()
    }

    #[flux::spec(fn () -> bool[<F as Foo>::f2()])]
    fn foo_bar_baz() -> bool {
        Self::implies()
    }
}
