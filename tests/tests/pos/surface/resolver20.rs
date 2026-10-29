//! Paths starting with `self` resolve relative to the current module, both in glob imports and in
//! signatures.

mod m {
    #[flux::refined_by(n: int)]
    pub struct S {
        #[flux::field(i32[n])]
        pub x: i32,
    }

    pub mod inner {
        #[flux::refined_by(b: bool)]
        pub struct T {
            #[flux::field(bool[b])]
            pub b: bool,
        }
    }

    // `self` is the enclosing module, not the crate root
    #[flux::sig(fn(self::inner::T[true]))]
    pub fn in_mod(_t: inner::T) {}
}

use self::m::*;

#[flux::sig(fn(S[0]))]
pub fn glob(_s: S) {}

#[flux::sig(fn(self::m::S[0]))]
pub fn path(_s: m::S) {}
