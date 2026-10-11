//! Regression test for https://github.com/flux-rs/flux/issues/1756
//!
//! Upvars are the only channel through which the enclosing frame's types reach a closure body:
//! they are embedded in `Ty::closure(..)`, which `to_closure_sig` turns into the closure's `self`
//! parameter. A `TyKind::Ptr` names a location that only means something in the frame that owns
//! it, so a `ptr` surviving into a closure dangles and `get_loc` reports `loc not found`.
//!
//! `closure_template` used to strip only a *top-level* `Ptr`, which missed every nested case
//! below. It now relates each upvar against the declared (rustc) upvar type refined with holes:
//! that target is location-free by construction, so subtyping converts every `Ptr` at any depth,
//! exactly as it does when checking a call against a function's formals.

pub trait Buf {
    fn remaining(&self) -> usize;
    fn advance(&mut self, cnt: usize);

    // `Self` is implicitly `?Sized`, so `&mut Self: Buf` and `self.remaining()` resolves to
    // `<&mut Self as Buf>::remaining`, which autorefs the local rather than `*self`. The closure
    // then captures `self` itself, making the upvar `&mut &mut Self` -- a nested `ptr`.
    fn get_u16(&mut self) -> usize {
        (|| {
            let n = self.remaining();
            self.advance(2);
            n
        })()
    }
}

impl<T: Buf + ?Sized> Buf for &mut T {
    fn remaining(&self) -> usize {
        (**self).remaining()
    }
    fn advance(&mut self, cnt: usize) {
        (**self).advance(cnt)
    }
}

// A `ptr` inside a tuple: the upvar's top level is a `Tuple`, so the old top-level match missed it.
fn use_tup(_t: &(&mut i32, &mut i32)) {}

pub fn tuple_by_value() {
    let mut x = 1i32;
    let mut y = 2i32;
    let t = (&mut x, &mut y);
    let c = move || use_tup(&t);
    c();
}

pub fn tuple_by_ref() {
    let mut x = 1i32;
    let mut y = 2i32;
    let t = (&mut x, &mut y);
    let c = || use_tup(&t);
    c();
}

// A `ptr` underneath a shared reference.
fn use_nested(_x: &&mut &mut i32) {}

pub fn nested_refs() {
    let mut x = 1i32;
    let mut r1 = &mut x;
    let r2 = &mut r1;
    let c = || use_nested(&r2);
    c();
}

// A `ptr` inside an array.
fn use_arr(_a: &[&mut i32; 2]) {}

pub fn array_of_mut() {
    let mut x = 1i32;
    let mut y = 2i32;
    let a = [&mut x, &mut y];
    let c = move || use_arr(&a);
    c();
}

// Upvars that never carried a location: these already worked and must keep working.
pub struct S<'a> {
    pub a: &'a mut i32,
}
fn use_s(_s: &S) {}

pub fn struct_upvar() {
    let mut x = 1i32;
    let s = S { a: &mut x };
    let c = move || use_s(&s);
    c();
}

fn use_one(_x: &mut i32) {}

pub fn single_mut() {
    let mut x = 1i32;
    let mut c = || use_one(&mut x);
    c();
}
