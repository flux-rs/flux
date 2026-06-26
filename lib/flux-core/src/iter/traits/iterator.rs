use flux_attrs::*;

defs! {
    fn default_iterator_size<T>(self: T) -> int;
    fn default_iterator_done<T>(self: T) -> bool;
    fn max(a: int, b: int) -> int { if a > b { a } else { b } }
}

#[extern_spec(core::iter)]
#[assoc(
    fn valid_item(self: Self, item: Self::Item) -> bool { true }
    fn size(self: Self) -> int { default_iterator_size(self) }
    fn done(self: Self) -> bool { default_iterator_done(self) }
    fn step(self: Self, other: Self) -> bool { true }
)]
trait Iterator {
    #[spec(
        fn(self: &mut Self[@curr_s]) -> Option<Self::Item>[!<Self as Iterator>::done(curr_s)]
        ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)}
    )]
    fn next(&mut self) -> Option<Self::Item>;

    #[spec(fn(Self[@s]) -> Enumerate<Self>[0, s])]
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized;

    #[spec(
        fn(Self[@s], f: F) -> Map<Self, F>[s]
        where
            F: FnMut(Self::Item{item: <Self as Iterator>::valid_item(s, item)}) -> B
    )]
    fn map<B, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B;

    #[spec(fn(Self[@s], n: usize) -> Skip<Self>[max(0, <Self as Iterator>::size(s) - n)])]
    fn skip(self, n: usize) -> Skip<Self>
    where
        Self: Sized;

    #[spec(fn(Self[@s], f: F) where F: FnMut(Self::Item{item: <Self as Iterator>::valid_item(s, item)}) -> () )]
    fn for_each<F>(self, f: F)
    where
        Self: Sized,
        F: FnMut(Self::Item);

    #[spec(fn (Self[@s]) -> B{v: <B as FromIterator<Self::Item>>::with_size(v, <Self as Iterator>::size(s))})]
    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/iter/traits/iterator.rs#L3049
    #[spec(fn(self: &mut Self[@s], P) -> Option<usize{n: n < <Self as Iterator>::size(s)}>
           where P: FnMut(Self::Item) -> bool)]
    fn position<P>(&mut self, predicate: P) -> Option<usize>
    where
        Self: Sized,
        P: FnMut(Self::Item) -> bool;
}
