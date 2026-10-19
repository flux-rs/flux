//! Imports nested several levels deep inside a `use` tree. The path of each nested tree is
//! relative to its parent, so resolving a nested glob requires the segments of all enclosing
//! trees.
#![allow(dead_code, unused_imports)]

mod outer {
    pub mod mid {
        pub mod inner {
            #[flux::refined_by(n: int)]
            pub struct S {
                #[flux::field(i32[n])]
                pub val: i32,
            }
        }

        #[flux::refined_by(b: bool)]
        pub struct T {
            #[flux::field(bool[b])]
            pub flag: bool,
        }
    }
}

mod nested_glob {
    use crate::outer::{mid::{inner::*}};

    #[flux::sig(fn(x: S[1]) -> i32[1])]
    fn test(x: S) -> i32 {
        x.val
    }
}

mod nested_single {
    use crate::{outer::{mid::T as U}};

    #[flux::sig(fn(x: U[true]) -> bool[true])]
    fn test(x: U) -> bool {
        x.flag
    }
}
