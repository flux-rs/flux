// test that we don't import private items from a glob import

mod a {
    struct S {}
}

use a::*;

#[flux::sig(fn(x: S))] //~ERROR cannot find type `S` in this scope
fn foo(x: i32) {}
