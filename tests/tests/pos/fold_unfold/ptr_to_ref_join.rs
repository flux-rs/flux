// Regression test for the points-to analysis used to insert `ptr_to_ref` ghost statements.
//
// The analysis tracked the base `Loc` a reference points to, so a borrow of a *field*, e.g.
// `&mut s.foo`, could not be represented and was mapped to `⊤`. No `ptr_to_ref` was then emitted
// at a join, and the checker crashed joining a `ptr` against another `ptr` with a different path
// (`two_fields`) or against a `&mut` (`field_and_local`).

#![flux::opts(scrape_quals = true)]

#[flux::refined_by(foo: int, bar: int)]
struct Foo {
    #[flux::field(usize[foo])]
    foo: usize,
    #[flux::field(usize[bar])]
    bar: usize,
}

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

#[flux::sig(fn(x: &mut usize{v: v >= 10}))]
fn bump(x: &mut usize) {
    *x = 20;
}

// Borrows of two *different fields* of the same local: `ptr(mut, s.0)` joined with `ptr(mut, s.1)`.
#[flux::sig(fn(bool, Foo[@n]) requires n.foo >= 10 && n.bar >= 10)]
fn two_fields(b: bool, mut s: Foo) {
    let r = if b { &mut s.foo } else { &mut s.bar };
    bump(r);
    assert(s.foo >= 10);
    assert(s.bar >= 10);
}

// A field of a local joined with a whole local: `ptr(mut, s.1)` joined with `ptr(mut, z)`.
#[flux::sig(fn(bool, Foo[@n], z: usize{v: v >= 10}) requires n.bar >= 10)]
fn field_and_local(b: bool, mut s: Foo, mut z: usize) {
    let r = if b { &mut s.bar } else { &mut z };
    bump(r);
    assert(s.bar >= 10);
    assert(z >= 10);
}
