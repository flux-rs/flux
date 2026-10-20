use flux_attrs::*;

// A `defs!` is resolved once, in the block declaring it, no matter how many blocks the function
// has, so its errors are reported once.
pub fn reported_once(b: bool) -> i32 {
    defs! {
        fn bad(x: int) -> int { x + nope } //~ ERROR cannot find value `nope` in this scope
    }
    if b {
        { 1 }
    } else {
        loop {
            break 2;
        }
    }
}

// Flux items are only visible in the block declaring them (and blocks nested in it).
pub fn not_visible_outside_block() {
    {
        defs! {
            fn inner(x: int) -> int { x }
        }
    }

    #[flux::sig(fn(x: i32) -> i32[inner(x)])] //~ ERROR cannot find value `inner` in this scope
    fn uses_inner(x: i32) -> i32 {
        x
    }
}

// Two `defs!` in the same block share a scope, so their names clash.
pub fn same_block() {
    defs! {
        fn dup(x: int) -> int { x }
    }
    defs! {
        fn dup(x: int) -> int { x } //~ ERROR the name `dup` is defined multiple times
    }
}
