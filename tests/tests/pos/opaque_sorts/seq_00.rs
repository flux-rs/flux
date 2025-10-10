use flux_rs::*;

defs! {
    opaque sort Seq<T>;
    fn nil<T>() -> Seq<T>;
    fn cons<T>(v: T, tail: Seq<T>) -> Seq<T>;
}

/// The elements of the inner vec in reverse order
#[opaque]
#[refined_by(elems: Seq<T>)]
struct Foo<T> {
    inner: Vec<T>
}

impl<T> Foo<T> {
    #[trusted]
    #[sig(fn() -> Self[nil()])]
    pub fn new() -> Self {
        Self {
            inner: Vec::new()
        }
    }

    #[trusted]
    #[sig(fn(self: &mut Self[@elems], elem: T[@v]) ensures self : Self[cons(v, elems)])]
    pub fn push(&mut self, v: T) {
        self.inner.push(v)
    }
}

#[sig(fn() -> Foo<i32>[nil()])]
fn test_empty() -> Foo<i32> {
    Foo::new()
}

#[sig(fn() -> Foo<bool>[cons(false, nil())])]
fn test_cons() -> Foo<bool> {
    let mut list = Foo::new();
    list.push(false);
    list
}





