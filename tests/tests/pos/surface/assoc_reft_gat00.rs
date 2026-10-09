// Refinements on the bound of a (generic) associated type. Lifetime arguments are elided in
// refinement paths, e.g., `Searcher` stands for `Searcher<'_>`.

use flux_attrs::*;

#[assoc(fn inv(s: Self) -> bool)]
pub trait Searcher<'a> {}

pub trait Pat: Sized {
    type S<'a>: Searcher<'a>;
    #[spec(fn(Self, &str) -> Self::S{s: <Self::S as Searcher>::inv(s)})]
    fn into_s<'a>(self, h: &'a str) -> Self::S<'a>;
}

pub struct CS<'a> { pub h: &'a str }
#[assoc(fn inv(s: CS) -> bool { true })]
impl<'a> Searcher<'a> for CS<'a> {}

impl Pat for char {
    type S<'a> = CS<'a>;
    #[spec(fn(char, &str) -> CS{s: <CS as Searcher>::inv(s)})]
    fn into_s<'a>(self, h: &'a str) -> CS<'a> { CS { h } }
}

#[spec(fn(T{v: <T as Searcher>::inv(v)}))]
pub fn needs<'a, T: Searcher<'a>>(_s: T) {}

pub fn use_contract<P: Pat>(p: P, h: &str) {
    let s = p.into_s(h);
    needs(s);
}
