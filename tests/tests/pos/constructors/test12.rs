use flux_rs::*;

#[flux::refined_by(start: T, end: T)]
struct Range<T> {
    #[flux::field(T[start])]
    pub start: T,
    #[flux::field(T[end])]
    pub end: T,
}

#[flux::sig(fn(r: Range<T>[@old]) -> Range<T>[{ ..old }])]
fn foo<T>(r: Range<T>) -> Range<T> {
    r
}

#[sig(fn(r: Range<i32>{v: v == Range { start: 0, end: 0 } }))]
fn foo2(_r: Range<i32>) {}
