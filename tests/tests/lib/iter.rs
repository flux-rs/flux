use flux_rs::extern_spec;

// Specs for std::slice::Iter and Enumerate
#[extern_spec(std::slice)]
#[refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[extern_spec(std::iter)]
#[refined_by(idx: int, inner: I)]
struct Enumerate<I>;

#[extern_spec(std::iter)]
#[flux::generics(Self as base)]
#[flux::assoc(fn done(self: Self) -> bool )]
#[flux::assoc(fn step(self: Self, other: Self) -> bool )]
trait Iterator {
    #[flux::sig(fn(self: &strg Self[@curr_s]) -> Option<Self::Item>[!<Self as Iterator>::done(curr_s)] ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<Self::Item>;

    #[flux::sig(fn(Self[@s]) -> Enumerate<Self>[0, s])]
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized;
}

#[extern_spec(std::slice)]
#[flux::generics(T as base)]
#[flux::assoc(fn done(x: Iter) -> bool { x.idx >= x.len })]
#[flux::assoc(fn step(x: Iter, y: Iter) -> bool { x.idx + 1 == y.idx && x.len == y.len})]
impl<'a, T> Iterator for Iter<'a, T> {
    #[flux::sig(fn(self: &strg Iter<T>[@curr_s]) -> Option<_>[curr_s.idx < curr_s.len] ensures self: Iter<T>{next_s: curr_s.idx + 1 == next_s.idx && curr_s.len == next_s.len})]
    fn next(&mut self) -> Option<&'a T>;
}

#[extern_spec(std::iter)]
#[flux::generics(I as base)]
#[flux::assoc(fn done(x: Enumerate<I>) -> bool { <I as Iterator>::done(x.inner)})]
#[flux::assoc(fn step(x: Enumerate<I>, y: Enumerate<I>) -> bool { <I as Iterator>::step(x.inner, y.inner)})]
impl<I: Iterator> Iterator for Enumerate<I> {
    #[flux::sig(fn(self: &strg Enumerate<I>[@curr_s]) -> Option<(usize[curr_s.idx], _)>[!<I as Iterator>::done(curr_s.inner)]
    ensures self: Enumerate<I>{next_s: curr_s.idx + 1 == next_s.idx && <I as Iterator>::step(curr_s.inner, next_s.inner)})]
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>;
}
