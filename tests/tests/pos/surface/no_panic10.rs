// Regression: promoted constants must not produce no-panic errors, regardless of whether the
// enclosing function is `no_panic`. rustc only promotes infallible operations in fn bodies (calls
// only to `#[rustc_promotable]` const fns), so promoted constants cannot panic.

pub fn promoted() {
    let _ = &core::mem::size_of::<usize>();
}

#[flux::no_panic]
pub fn promoted_no_panic() {
    let _ = &core::mem::size_of::<usize>();
}
