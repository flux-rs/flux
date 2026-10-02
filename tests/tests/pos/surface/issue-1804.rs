//! Regression test for https://github.com/flux-rs/flux/issues/1804
//!
//! The sort of an associated refinement must be instantiated with the alias's generic args
//! before encoding it in fixpoint. Otherwise `T` stays a sort parameter and gets encoded as
//! `int`, while the argument passed for `out` here has `W`'s (ADT) sort.

#[flux::refined_by(n: int)]
pub struct W {
    #[flux::field(usize[n])]
    pub n: usize,
}

#[flux::assoc(fn rel(s: Self, out: T) -> bool { true })]
pub trait Conv<T>: Sized {
    #[flux::sig(fn(Self[@s]) -> T{v: <Self as Conv<T>>::rel(s, v)})]
    fn conv(self) -> T;
}

// Unpacking and repacking `W` keeps the constraint from being simplified away.
#[flux::sig(fn(A[@s]) -> W{v: <A as Conv<W>>::rel(s, v)})]
pub fn g<A: Conv<W>>(a: A) -> W {
    let w = a.conv();
    W { n: w.n }
}
