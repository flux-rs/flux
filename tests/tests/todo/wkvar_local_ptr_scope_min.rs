// Minimized from `wkvar_local_ptr_scope.rs`. The signature of `foo` mimics the one produced by
// inserting weak kvars: the generic argument of `S` depends on the (existential) index of `S`.
// Run with `cargo x run tests/tests/todo/wkvar_local_ptr_scope_min.rs`.
#[flux::opaque]
#[flux::refined_by(n: int)]
pub struct S<T> {
    x: T,
}

pub enum E {
    A,
    B,
}

#[flux::sig(fn(&mut {n. S<{v. i32[v] | v <= n}>[n] | n >= 0}))]
fn foo(_: &mut S<i32>) {}

pub fn test(s: &mut S<i32>, e: E) -> i32 {
    match e {
        E::A => foo(s),
        E::B => {}
    }
    0
}
