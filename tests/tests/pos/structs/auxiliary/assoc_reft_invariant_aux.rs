#[flux::assoc(fn min() -> int)]
pub trait HasMin {}

#[flux::refined_by(n: int)]
#[flux::invariant(n >= <Foo as HasMin>::min())]
pub struct Foo {
    #[flux::field(usize[n])]
    pub value: usize,
}

#[flux::assoc(fn min() -> int {1})]
impl HasMin for Foo {}

pub fn make_foo() -> Foo {
    Foo { value: 1 }
}
