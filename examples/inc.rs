#![feature(register_tool)]
#![register_tool(liquid)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

#[liquid::ty("fn(n: int) -> {v: int | v == n + 1}")]
fn inc(n: u32) -> u32 {
    n + 1
}

#[liquid::ty("fn(n: int) -> {v: int | v >= 0}")]
fn abs(mut n: u32) -> u32 {
    if n < 0 {
        n = 0 - n;
    }
    n
}

#[liquid::ty("fn(n: {n: int | n >= 0}) -> {v: int | v >= n}")]
fn sum(n: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i <= n {
        s += i;
        i += 1;
    }
    s
}

fn main() {}
