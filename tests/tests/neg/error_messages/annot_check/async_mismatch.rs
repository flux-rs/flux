#![allow(unused)]

use flux_rs::attrs::*;
// This should fail because Rust is async but Flux signature is not
#[flux::sig(fn(x: i32) -> i32)] //~ ERROR function has an incompatible refinement annotation
async fn missing_async(x: i32) -> i32 {
    x
}

// Original test from issue https://github.com/flux-rs/flux/issues/1404

#[refined_by(val: int)]
struct Msg(#[field(i32[val])] i32);

#[sig(fn(x: i32{x > 0}) -> Msg[x])] //~ ERROR function has an incompatible refinement annotation
async fn send_msg(x: i32) -> Msg {
    Msg(x)
}
