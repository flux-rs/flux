//! Companion to `neg/surface/resolver13.rs`: the cases where competing glob imports must *not* be
//! reported as ambiguous.
#![allow(dead_code, unused_imports)]

// Case 0: two globs bringing in the *same* item through different paths. Not a conflict, in flux
// or in rustc.
mod inner {
    pub struct S;
}

mod re1 {
    pub use super::inner::S;
}

mod re2 {
    pub use super::inner::S;
}

mod same_item_twice {
    use super::{re1::*, re2::*};

    #[flux::sig(fn(x: S))]
    fn test(x: S) {}
}

// Case 1: an explicit import shadows a glob import of a different item with the same name, in
// *either* declaration order. `resolver12.rs` covers explicit-first; this is glob-first, which
// order-dependent shadowing would get wrong.
mod a {
    #[flux::sig(fn(x: i32) -> i32[x + 1])]
    pub fn shift(x: i32) -> i32 {
        x + 1
    }
}

mod b {
    #[flux::sig(fn(x: i32) -> i32[x + 2])]
    pub fn shift(x: i32) -> i32 {
        x + 2
    }
}

mod glob_first {
    use super::b::*;

    use super::a::shift;

    // `x + 1` (from the explicit `a::shift`), not `x + 2`.
    #[flux::sig(fn(x: i32) -> i32[x + 1])]
    pub fn test(x: i32) -> i32 {
        shift(x)
    }
}

// Case 2: a locally defined item shadows a glob import of a same-named item, and the local one is
// what flux paths resolve to.
mod other {
    #[flux::refined_by(n: int)]
    pub struct S {
        #[flux::field(i32[n])]
        pub val: i32,
    }
}

mod local_item_wins {
    use super::other::*;

    // Shadows the glob-imported `other::S`, which is indexed by an `int` rather than a `bool`, so
    // the signature below would not even sort-check if resolution picked the wrong one.
    #[flux::refined_by(b: bool)]
    pub struct S {
        #[flux::field(bool[b])]
        pub flag: bool,
    }

    #[flux::sig(fn(x: S[true]) -> bool[true])]
    pub fn test(x: S) -> bool {
        x.flag
    }
}
