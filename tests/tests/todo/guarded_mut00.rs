#[flux::refined_by(foo: int, bar: int)]
#[flux::invariant(foo <= bar)]
struct Foo {
    #[flux::field(usize[foo])]
    foo: usize,
    #[flux::field(usize[bar])]
    bar: usize,
}

#[flux::sig(fn(s: &mut Foo[@me]) -> &mut usize{v: me.foo <= v} ensures s: Foo)] // want callers to "block s"
fn test_ok(s: &mut Foo) -> &mut usize {
    &mut s.bar
}

#[flux::sig(fn(s: &mut Foo[@me]) -> &mut usize ensures s: Foo)] // want callers to "block s"
fn test_fail(s: &mut Foo) -> &mut usize {
    &mut s.bar
}
