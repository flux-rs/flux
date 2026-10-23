// An invariant on a struct referring to an associated refinement on the same struct.
// See https://github.com/flux-rs/flux/issues/1797

#[flux::refined_by(n: int)]
#[flux::invariant(n >= <Foo as Sized>::size_of())]
pub struct Foo {
    #[flux::field(usize[n])]
    value: usize,
}

pub fn make() -> Foo {
    Foo { value: 8 }
}

#[flux::sig(fn(Foo) -> usize{v: v >= 8})]
pub fn get(foo: Foo) -> usize {
    foo.value
}
