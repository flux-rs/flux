//! Regression test for https://github.com/flux-rs/flux/issues/1754
//!
//! `Self` is implicitly `?Sized` in a trait definition, so with `impl<T: Buf + ?Sized> Buf for
//! &mut T` the type `&mut Self` itself implements `Buf`. Method resolution on `self.remaining()`
//! therefore picks `<&mut Self as Buf>::remaining`, which takes `&&mut Self` and so autorefs the
//! *local* holding `ptr(mut, l)` rather than `*self`.
//!
//! Relating `&ptr(mut, l)` against `&(&mut Self)` used to convert the pointer to a `&mut` and
//! block `l`, and nothing ever unblocked it: the borrow responsible is shared, so no `Unblock`
//! ghost statement is emitted for it. The later `self.advance(1)` then saw a blocked type.
//! A `&mut` underneath a shared reference cannot be used to mutate, so we no longer block.

pub trait Buf {
    fn remaining(&self) -> usize;
    fn advance(&mut self, cnt: usize);

    fn get_u8(&mut self) -> usize {
        let n = self.remaining(); // shared reborrow of `self`
        self.advance(1); // mutable reborrow of `self`
        n
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

// A `ptr` nested under a *shared* reference: the location must keep its precise type, because
// it is not blocked.
fn read_shared_nested(_x: &&mut i32) {}

#[flux::sig(fn(x: &mut i32[@n]) ensures x: i32[n])]
fn keeps_index(x: &mut i32) {
    read_shared_nested(&x);
}

// A `ptr` nested under a `&mut`: this used to ICE with "call to `ptr_to_ref` on `DummyEnv`",
// because `TypeEnv::ptr_to_ref` related the location's type against the bound using a `DummyEnv`.
fn read_mut_nested(x: &mut &mut i32) -> i32 {
    **x
}

fn call_mut_nested(mut x: &mut i32) -> i32 {
    let b = read_mut_nested(&mut x);
    *x = 4;
    b
}
