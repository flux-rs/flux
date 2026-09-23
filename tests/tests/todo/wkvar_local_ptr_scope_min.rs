// Minimized from `wkvar_local_ptr_scope.rs`.
// Run with `cargo x --suggestions run tests/tests/todo/wkvar_local_ptr_scope_min.rs`.
#[flux::opaque]
#[flux::refined_by(n: int)]
pub struct S<T> {
    x: T,
}

pub enum E {
    A,
    B,
}

fn foo(_: &mut S<i32>) {}

pub fn test(s: &mut S<i32>, e: E) -> i32 {
    match e {
        E::A => foo(s),
        E::B => {}
    }
    0
}
