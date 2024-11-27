use flux_rs::*;

#[refined_by(start: T, end: T)]
struct Range<T> {
    #[field(T[start])]
    pub start: T,
    #[field(T[end])]
    pub end: T,
}

#[sig(fn(r: Range<bool>{v: Range { start: 0, end: 0 } == v }))] //~ERROR: mismatched sorts
fn foo(_r: Range<i32>) {}
