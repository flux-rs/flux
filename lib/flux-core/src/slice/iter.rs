use flux_attrs::*;

#[extern_spec(core::slice)]
#[refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[extern_spec(core::slice)]
impl<'a, T> Iter<'a, T> {
    #[no_panic]
    #[spec(fn(&Self[@it]) -> &[T][it.len])]
    fn as_slice(&self) -> &'a [T];
}

#[extern_spec(core::slice)]
#[assoc(
    fn size(x: Iter) -> int { x.len - x.idx }
    fn done(x: Iter) -> bool { x.idx >= x.len }
    fn step(x: Iter, y: Iter) -> bool { x.idx + 1 == y.idx && x.len == y.len}
)]
impl<'a, T> Iterator for Iter<'a, T> {
    #[no_panic]
    #[spec(fn(self: &mut Iter<T>[@curr_s]) -> Option<_>[curr_s.idx < curr_s.len]
           ensures self: Iter<T>{next_s: curr_s.idx + 1 == next_s.idx && curr_s.len == next_s.len})]
    fn next(&mut self) -> Option<&'a T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/iter/traits/iterator.rs#L3049
    #[spec(fn(self: &mut Iter<T>[@s], P) -> Option<usize{n: n < s.len - s.idx}>)]
    fn position<P>(&mut self, predicate: P) -> Option<usize>
    where
        Self: Sized,
        P: FnMut(&'a T) -> bool;
}

#[extern_spec(core::slice)]
impl<'a, T> IntoIterator for &'a [T] {
    #[no_panic]
    #[spec(fn(&[T][@n]) -> Iter<T>[0, n])]
    fn into_iter(v: &'a [T]) -> Iter<'a, T>;
}

#[extern_spec(core::slice)]
#[refined_by(remaining: int, window_size: int)]
struct Windows<'a, T>;

#[extern_spec(core::slice)]
#[assoc(
    fn size(x: Windows) -> int { if x.window_size > x.remaining { 0 } else { x.remaining - x.window_size + 1 } }
    fn done(x: Windows) -> bool { x.remaining < x.window_size }
    fn step(x: Windows, y: Windows) -> bool { y.remaining == x.remaining - 1 && y.window_size == x.window_size }
)]
impl<'a, T> Iterator for Windows<'a, T> {
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/iter.rs#L1356
    #[no_panic]
    #[spec(fn(self: &mut Windows<T>[@curr_s]) -> Option<&[T][curr_s.window_size]>[curr_s.remaining >= curr_s.window_size]
           ensures self: Windows<T>{next_s: next_s.remaining == curr_s.remaining - 1 && next_s.window_size == curr_s.window_size})]
    fn next(&mut self) -> Option<&'a [T]>;
}
