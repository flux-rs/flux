#![allow(unused)]
extern crate flux_rs;

// This should fail because Rust is async but Flux signature is not
#[flux::sig(fn(x: i32) -> i32)] //~ ERROR function signature asyncness mismatch
async fn missing_async(x: i32) -> i32 {
    x
}
