// Returning a `&mut` into a field of a `&strg` (i.e. `&mut` + `ensures`) argument. The returned
// reference *guards* the field: folding the struct back to check the `ensures` clause uses the
// guard as the type of the field, so the guard has to be strong enough to re-establish the
// struct's invariant.

#[flux::refined_by(foo: int, bar: int)]
#[flux::invariant(foo <= bar)]
pub struct Foo {
    #[flux::field(usize[foo])]
    foo: usize,
    #[flux::field(usize[bar])]
    bar: usize,
}

#[flux::refined_by(inner: Foo, n: int)]
pub struct Outer {
    #[flux::field(Foo[inner])]
    inner: Foo,
    #[flux::field(usize[n])]
    n: usize,
}

#[flux::sig(fn(s: &mut Foo[@me]) -> &mut usize{v: me.foo <= v} ensures s: Foo)]
pub fn test00(s: &mut Foo) -> &mut usize {
    &mut s.bar
}

#[flux::sig(fn(s: &mut Foo[@me]) -> &mut usize{v: me.foo <= v} ensures s: Foo)]
pub fn test01(s: &mut Foo) -> &mut usize {
    s.bar += 1;
    &mut s.bar
}

// nested field
#[flux::sig(fn(s: &mut Outer[@me]) -> &mut usize{v: me.inner.foo <= v} ensures s: Outer)]
pub fn test02(s: &mut Outer) -> &mut usize {
    &mut s.inner.bar
}

// no guard needed because no invariant mentions `n`
#[flux::sig(fn(s: &mut Outer[@me]) -> &mut usize ensures s: Outer)]
pub fn test03(s: &mut Outer) -> &mut usize {
    &mut s.n
}

// the whole argument is borrowed, not just a field
#[flux::sig(fn(s: &mut Foo[@me]) -> &mut Foo{v: me.foo <= v.foo} ensures s: Foo)]
pub fn test04(s: &mut Foo) -> &mut Foo {
    s
}

// tuples
#[flux::sig(fn(s: &mut (usize[@a], usize)) -> &mut usize ensures s: (usize[a], usize))]
pub fn test05(s: &mut (usize, usize)) -> &mut usize {
    &mut s.1
}

#[flux::refined_by(inner: Foo, n: int)]
#[flux::invariant(n <= inner.bar)]
pub struct OuterInv {
    #[flux::field(Foo[inner])]
    inner: Foo,
    #[flux::field(usize[n])]
    n: usize,
}

// nested field
#[flux::sig(fn(s: &mut OuterInv[@me]) -> &mut usize{v: me.inner.bar <= v} ensures s: OuterInv)]
pub fn test02_nested_inv2(s: &mut OuterInv) -> &mut usize {
    &mut s.inner.bar
}

#[flux::refined_by(inner: Foo, n: int)]
#[flux::invariant(n <= inner.foo)]
pub struct OuterInv1 {
    #[flux::field(Foo[inner])]
    inner: Foo,
    #[flux::field(usize[n])]
    n: usize,
}

// nested field
#[flux::sig(fn(s: &mut OuterInv1[@me]) -> &mut usize{v: me.inner.foo <= v} ensures s: OuterInv1)]
pub fn test02_nested_inv1(s: &mut OuterInv1) -> &mut usize {
    &mut s.inner.bar
}
