// The guard on the returned `&mut` is too weak to re-establish the invariant of the struct when
// it is folded back to check the `ensures` clause.

#[flux::refined_by(foo: int, bar: int)]
#[flux::invariant(foo <= bar)] //~ NOTE this is the condition
//~| NOTE this is the condition
//~| NOTE this is the condition
struct Foo {
    #[flux::field(usize[foo])]
    foo: usize,
    #[flux::field(usize[bar])]
    bar: usize,
}

#[flux::refined_by(inner: Foo, n: int)]
struct Outer {
    #[flux::field(Foo[inner])]
    inner: Foo,
    #[flux::field(usize[n])]
    n: usize,
}

#[flux::sig(fn(s: &mut Foo[@me]) -> &mut usize ensures s: Foo)]
fn test00(s: &mut Foo) -> &mut usize {
    &mut s.bar
} //~ ERROR type invariant may not hold

// the guard holds of the current value of `bar` but is not strong enough: it still allows writing
// a value below `me.foo`
#[flux::sig(fn(s: &mut Foo[@me]) -> &mut usize{v: v + 1 >= me.foo} ensures s: Foo)]
fn test01(s: &mut Foo) -> &mut usize {
    &mut s.bar
} //~ ERROR type invariant may not hold

// nested field
#[flux::sig(fn(s: &mut Outer[@me]) -> &mut usize ensures s: Outer)]
fn test02(s: &mut Outer) -> &mut usize {
    &mut s.inner.bar
} //~ ERROR type invariant may not hold
