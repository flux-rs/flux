#![feature(step_trait)]
#![allow(unused)]

#[path = "../../lib/iterator.rs"]
mod iterator;

#[flux_rs::sig(fn (bool[true]))]
fn assert(b: bool) {}

fn donald() {
    let n: i32 = 10;
    let mut thing = 0..n;
    let a = thing.next().unwrap();
    assert(a == 0);
    let b = thing.next().unwrap();
    assert(b == 1);
    let c = thing.next().unwrap();
    assert(c == 2);
}

#[flux_rs::sig(fn (n:i32{n == 99}))]
fn goofy(n: i32) {
    let mut thing = 0..n;
    let a0 = thing.end;
    assert(a0 == n);
    while let Some(i) = thing.next() {
        assert(0 <= i);
        assert(i < n);
    }
}

#[flux_rs::sig(fn (n:i32{n == 99}))]
fn mickey(n: i32) {
    for i in 0..n {
        assert(0 <= i);
        assert(i < n);
    }
}
