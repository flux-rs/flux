//! Flux items declared by a `defs!` inside a function body are scoped to the block containing
//! the `defs!`, like block-local Rust items.
#![allow(dead_code)]

use flux_attrs::*;

// Each block has its own `k`. If they were conflated, one of the signatures wouldn't verify.
pub fn sibling_blocks() {
    {
        defs! {
            fn k(x: int) -> int { x }
        }

        #[flux::sig(fn(x: i32) -> i32[k(x)])]
        fn one(x: i32) -> i32 {
            x
        }
    }
    {
        defs! {
            fn k(x: int) -> int { 0 }
        }

        #[flux::sig(fn(x: i32) -> i32[k(x)])]
        fn two(_x: i32) -> i32 {
            0
        }
    }
}

// A def in a nested block shadows one in an enclosing block.
pub fn shadowing() {
    defs! {
        fn k(x: int) -> int { x }
    }

    #[flux::sig(fn(x: i32) -> i32[k(x)])]
    fn outer(x: i32) -> i32 {
        x
    }

    {
        defs! {
            fn k(x: int) -> int { 0 }
        }

        #[flux::sig(fn(x: i32) -> i32[k(x)])]
        fn inner(_x: i32) -> i32 {
            0
        }
    }
}

// Defs are visible in nested blocks, including closure bodies.
pub fn nested_blocks() {
    defs! {
        fn id(x: int) -> int { x }
    }

    if true {
        #[flux::sig(fn(x: i32) -> i32[id(x)])]
        fn in_if(x: i32) -> i32 {
            x
        }
    }

    let f = || {
        #[flux::sig(fn(x: i32) -> i32[id(x)])]
        fn in_closure(x: i32) -> i32 {
            x
        }
        in_closure(0)
    };
    f();
}

// A def can refer to items declared in the same block.
pub fn local_struct() {
    #[flux::refined_by(n: int)]
    struct S {
        #[flux::field(i32[n])]
        x: i32,
    }

    defs! {
        fn get(s: S) -> int { s.n }
    }

    #[flux::sig(fn(s: S) -> i32[get(s)])]
    fn read(s: S) -> i32 {
        s.x
    }
}
