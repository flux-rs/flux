use flux_rs::*;

#[flux::refined_by(start: T, end: T)]
struct Range<T> {
    #[flux::field(T[start])]
    pub start: T,
    #[flux::field(T[end])]
    pub end: T,
}

#[sig(fn(r: Range<i32>{v: v == Range { start: true, end: false } }))] //~ERROR mismatched sorts
fn foo2(_r: Range<i32>) {}
