// Regression test for https://github.com/flux-rs/flux/issues/1695
// An ill-sorted constraint was generated when using `no_panic_if` with a `Result` type
// because the ADT sort `{is_ok: bool}` was used instead of the flattened `bool` sort.

extern crate flux_core;

#[allow(unused)]
#[flux::no_panic_if(is_ok)]
#[flux::sig(fn(z: Result<i32, bool>[@is_ok]) -> i32)]
fn test(z: Result<i32, bool>) -> i32 {
    match z {
        Ok(n) => n,
        Err(_) => panic!("yikes"),
    }
}
