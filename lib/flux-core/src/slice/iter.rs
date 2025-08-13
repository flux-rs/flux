use flux_attrs::*;

#[extern_spec(core::slice)]
#[refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[extern_spec(core::slice)]
impl<'a, T> Iter<'a, T> {
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
    #[spec(fn(self: &mut Iter<T>[@curr_s]) -> Option<_>[curr_s.idx < curr_s.len]
           ensures self: Iter<T>{next_s: 
            (curr_s.idx < curr_s.len => curr_s.idx + 1 == next_s.idx && curr_s.len == next_s.len) &&
            (curr_s.idx >= curr_s.len => curr_s.idx == next_s.idx && curr_s.len == next_s.len) 
        })]
    fn next(&mut self) -> Option<&'a T>;
}

#[extern_spec(core::slice)]
impl<'a, T> IntoIterator for &'a [T] {
    #[spec(fn(&[T][@n]) -> Iter<T>[0, n])]
    fn into_iter(v: &'a [T]) -> Iter<'a, T>;
}
