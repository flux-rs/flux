#![allow(unused)]

#[flux::sig(fn (x: &strg i32[@n]) ensures x: i32[n+1])]
fn incr(x: &mut i32) {
    *x += 1;
}

#[flux::sig(fn (x: &mut i32{v: 0<=v}))]
fn client_safe(z: &mut i32) {
    incr(z);
}
