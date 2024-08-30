// Extern spec of a type with a lifetime

use std::slice::Iter;

use flux_rs::*;

#[extern_spec]
#[refined_by(len: int)]
struct Iter<'a, T>;

#[extern_spec]
impl<'a, T> Iter<'a, T> {
    #[spec(fn as_slice(&Iter<T>[@n]) -> &[T][n])]
    fn as_slice(v: &Iter<'a, T>) -> &'a [T];
}

#[extern_spec]
impl<T> [T] {
    #[spec(fn iter(&[T][@n]) -> Iter<T>[n])]
    fn iter(v: &[T]) -> Iter<'_, T>;
}

#[spec(fn test00(x: &[i32][@n]) -> &[i32][n])]
fn test00(x: &[i32]) -> &[i32] {
    x.iter().as_slice()
}
