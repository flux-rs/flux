use flux_attrs::*;

#[extern_spec(core::slice)]
#[refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[extern_spec(core::slice)]
impl<'a, T> Iter<'a, T> {
    #[sig(fn(&Self[@it]) -> &[T][it.len])]
    fn as_slice(&self) -> &'a [T];
}

#[extern_spec(core::slice)]
impl<'a, T> IntoIterator for &'a [T] {
    #[flux::sig(fn(&[T][@n]) -> Iter<T>[0, n])]
    fn into_iter(v: &'a [T]) -> Iter<'a, T>;
}
