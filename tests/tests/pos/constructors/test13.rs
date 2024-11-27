use flux_rs::*;

#[refined_by(start: T, end: T)]
struct Range<T> {
    #[field(T[start])]
    pub start: T,
    #[field(T[end])]
    pub end: T,
}

#[sig(fn(r: Range<i32>{v: Range { start: 0, end: 0 } == v }))]
fn foo(_r: Range<i32>) {}

#[refined_by(x: int, y: int)]
struct S {
    #[field(u32[x])]
    pub x: u32,
    #[field(u32[y])]
    pub y: u32,
}

#[sig(fn(s: S{v: S { x: 0, y: 0 } == v }))]
fn foo_concrete(_s: S) {}
