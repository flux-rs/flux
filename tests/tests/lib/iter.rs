use flux_rs::extern_spec;

// Specs for std::slice::Iter and Enumerate
#[extern_spec(std::slice)]
#[refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[extern_spec(std::iter)]
#[refined_by(idx: int, inner: I)]
struct Enumerate<I>;

#[extern_spec(std::iter)]
#[refined_by(inner: I)]
struct Map<I, F>;

#[extern_spec]
#[flux::assoc(fn with_size(self: Self, n:int) -> bool { true })] // default: don't know!
trait FromIterator<A> {}

#[extern_spec(std::iter)]
#[flux::assoc(fn valid_item(item: Self::Item) -> bool { true })]
#[flux::assoc(fn size(self: Self) -> int)]
#[flux::assoc(fn done(self: Self) -> bool)]
#[flux::assoc(fn step(self: Self, other: Self) -> bool)]
trait Iterator {
    #[flux::sig(fn(self: &strg Self[@curr_s]) -> Option<Self::Item>[!<Self as Iterator>::done(curr_s)] ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<Self::Item>;

    #[flux::sig(fn(Self[@s]) -> Enumerate<Self>[0, s])]
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized;

    #[flux::sig(fn(Self[@s], f: F) -> Map<Self, F>[s])]
    fn map<B, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B;

    #[flux::sig(fn (Self[@s]) -> B{v: <B as FromIterator<Self::Item>>::with_size(v, <Self as Iterator>::size(s))})]
    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized;
}

#[extern_spec(std::slice)]
#[flux::assoc(fn size(x: Iter) -> int { x.len - x.idx })]
#[flux::assoc(fn done(x: Iter) -> bool { x.idx >= x.len })]
#[flux::assoc(fn step(x: Iter, y: Iter) -> bool { x.idx + 1 == y.idx && x.len == y.len})]
impl<'a, T> Iterator for Iter<'a, T> {
    #[flux::sig(fn(self: &strg Iter<T>[@curr_s]) -> Option<_>[curr_s.idx < curr_s.len] ensures self: Iter<T>{next_s: curr_s.idx + 1 == next_s.idx && curr_s.len == next_s.len})]
    fn next(&mut self) -> Option<&'a T>;
}

#[extern_spec(std::iter)]
#[flux::assoc(fn size(x: Enumerate<I>) -> int { <I as Iterator>::size(x.inner) })]
#[flux::assoc(fn done(x: Enumerate<I>) -> bool { <I as Iterator>::done(x.inner)})]
#[flux::assoc(fn step(x: Enumerate<I>, y: Enumerate<I>) -> bool { <I as Iterator>::step(x.inner, y.inner)})]
impl<I: Iterator> Iterator for Enumerate<I> {
    #[flux::sig(fn(self: &strg Enumerate<I>[@curr_s]) -> Option<(usize[curr_s.idx], _)>[!<I as Iterator>::done(curr_s.inner)]
    ensures self: Enumerate<I>{next_s: curr_s.idx + 1 == next_s.idx && <I as Iterator>::step(curr_s.inner, next_s.inner)})]
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>;
}

#[extern_spec(std::iter)]
#[flux::assoc(fn size(x: Map<I>) -> int { <I as Iterator>::size(x.inner) })]
#[flux::assoc(fn done(x: Map<I>) -> bool { <I as Iterator>::done(x.inner)})]
#[flux::assoc(fn step(x: Map<I>, y: Map<I>) -> bool { <I as Iterator>::step(x.inner, y.inner)})]
impl<B, I: Iterator, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {} // orig: where F: FnMut(I::Item) -> B {}

// -------------------------------------------------------------------------------------------------------------------------------------

#[flux_rs::extern_spec(std::iter)]
trait IntoIterator {
    #[flux_rs::sig(fn(self: Self) -> Self::IntoIter)]
    fn into_iter(self) -> Self::IntoIter
    where
        Self: Sized;
}

#[flux_rs::extern_spec(core::ops)]
impl<I: Iterator> IntoIterator for I {
    #[flux_rs::sig(fn(self: I[@s]) -> I[s])]
    fn into_iter(self) -> I;
}
