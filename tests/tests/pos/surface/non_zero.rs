use std::num::NonZeroUsize;

fn foo(_z: NonZeroUsize) -> i32 {
    0
}

pub fn bar() -> i32 {
    foo(NonZeroUsize::MIN)
}
