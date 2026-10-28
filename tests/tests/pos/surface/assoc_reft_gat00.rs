// Lifetimes can't be written in flux paths, so the lifetime arguments of the GAT `Self::S` and
// of the trait `Searcher` in the qualified path must be elided and inferred.

#[flux::assoc(fn inv(s: Self) -> bool)]
pub trait Searcher<'a> {}

pub trait Pat: Sized {
    type S<'a>: Searcher<'a>;

    #[flux::sig(fn(Self, &str) -> Self::S{s: <Self::S as Searcher>::inv(s)})]
    fn into_s<'a>(self, h: &'a str) -> Self::S<'a>;
}

// Same for a GAT used as a sort.
#[flux::assoc(fn ok(x: Self::T) -> bool)]
pub trait Holder {
    type T<'a>;
}
