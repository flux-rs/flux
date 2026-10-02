#![allow(unused)]

#[flux::refined_by(n: int)]
#[flux::invariant(n >= <Foo as Sized>::size_of())]
pub struct Foo {
    #[flux::field(usize[n])]
    value: usize,
}

pub fn make_foo() -> Foo {
    Foo { value: 8 }
}

#[flux::assoc(fn min() -> int)]
trait HasMin {}

#[flux::refined_by(n: int)]
#[flux::invariant(n >= <Bar as HasMin>::min())]
struct Bar {
    #[flux::field(usize[n])]
    value: usize,
}

#[flux::assoc(fn min() -> int { 0 })]
impl HasMin for Bar {}

fn make_bar() -> Bar {
    Bar { value: 0 }
}
