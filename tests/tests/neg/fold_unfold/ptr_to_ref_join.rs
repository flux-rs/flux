// Negative counterpart to `pos/fold_unfold/ptr_to_ref_join.rs`.
//
// Same joins of a field borrow with another pointer, but now the refinements do not hold. Making
// the points-to analysis track the full path (so `ptr_to_ref` is emitted for field borrows) must
// not weaken the checker:
//
// - `two_fields` borrows a field whose value does not satisfy `bump`'s precondition,
// - `field_and_local` claims a field keeps its old value across a borrow that may overwrite it.

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

// `bar` is unconstrained, so the `else` branch cannot prove `bump`'s precondition.
#[flux::sig(fn(bool, Foo[@n]) requires n.foo >= 10)]
fn two_fields(b: bool, mut s: Foo) {
    let r = if b { &mut s.foo } else { &mut s.bar };
    bump(r); //~ ERROR refinement type
}

// `bump` may write through the reference, so `s.bar` is only known to satisfy the bound it was
// blocked with, not to have kept its original value.
#[flux::sig(fn(bool, Foo[@n], z: usize{v: v >= 10}) requires n.bar >= 10)]
fn field_and_local(b: bool, mut s: Foo, mut z: usize) {
    let old = s.bar;
    let r = if b { &mut s.bar } else { &mut z };
    bump(r);
    assert(s.bar == old); //~ ERROR refinement type
}
