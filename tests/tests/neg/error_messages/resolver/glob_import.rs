// test that we don't import private items from a glob import

mod a {
    struct S {}
}

use a::*;

#[flux::sig(fn(x: S))] //~ERROR cannot resolve
fn foo(x: i32) {}
