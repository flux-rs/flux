use flux_attrs::*;

#[extern_spec]
#[refined_by(is_some: bool)]
enum Option<T> {
    #[variant(Option<T>[false])]
    None,
    #[variant((T) -> Option<T>[true])]
    Some(T),
}

#[extern_spec]
impl<T> Option<T> {
    #[sig(fn(&Self[@b]) -> bool[b])]
    const fn is_some(&self) -> bool;

    #[sig(fn(&Self[@b]) -> bool[!b])]
    const fn is_none(&self) -> bool;

    #[no_panic]
    #[sig(fn(Option<T>[true]) -> T)]
    const fn unwrap(self) -> T;

    #[sig(fn(&Self[@b]) -> Option<&T>[b])]
    fn as_ref(&self) -> Option<&T>;

    #[sig(fn(&mut Self[@b]) -> Option<&mut T>[b])]
    fn as_mut(&mut self) -> Option<&mut T>;

    #[sig(fn(&Self[@b]) -> &[T][if b { 1 } else { 0 }])]
    fn as_slice(&self) -> &[T];

    #[sig(fn(&mut Self[@b]) -> &mut [T][if b { 1 } else { 0 }])]
    fn as_mut_slice(&mut self) -> &mut [T];
}
