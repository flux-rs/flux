use flux_rs::*;

#[refined_by(start: T, end: T)]
pub struct Range<T> {
    #[flux::field(T[start])]
    pub start: T,
    #[flux::field(T[end])]
    pub end: T,
}

#[sig(fn(r: Range<T>[@old]) -> Range<T>[ Range { ..old } ])]
pub fn foo<T>(r: Range<T>) -> Range<T> {
    r
}

#[sig(fn(r: Range<i32>{v: v == Range { start: 0, end: 0 } }))]
pub fn foo2(_r: Range<i32>) {}

#[sig(fn(r: Range<i32>[Range { start: 0, end: 0 } ]))]
pub fn foo3(_r: Range<i32>) {}
