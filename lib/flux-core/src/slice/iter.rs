use flux_attrs::*;

#[extern_spec(core::slice)]
#[refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[extern_spec(core::slice)]
impl<'a, T> Iter<'a, T> {
    #[sig(fn(&Self[@it]) -> &[T][it.len])]
    fn as_slice(&self) -> &'a [T];
}
