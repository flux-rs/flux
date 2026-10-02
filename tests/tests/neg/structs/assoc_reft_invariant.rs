#[flux::refined_by(n: int)]
#[flux::invariant(n >= <Foo as Sized>::size_of())]
struct Foo {
    #[flux::field(usize[n])]
    value: usize,
}

fn make_foo() -> Foo {
    Foo { value: 0 } //~ ERROR refinement type
}

#[flux::assoc(fn min() -> int)]
trait HasMin {}

#[flux::refined_by(n: int)]
#[flux::invariant(n >= <Bar as HasMin>::min())]
struct Bar {
    #[flux::field(usize[n])]
    value: usize,
}

#[flux::assoc(fn min() -> int { 1 })]
impl HasMin for Bar {}

fn make_bar() -> Bar {
    Bar { value: 0 } //~ ERROR refinement type
}
