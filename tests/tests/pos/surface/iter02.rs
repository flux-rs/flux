#![allow(unused)]
use std::slice::Iter;
use std::iter::Enumerate;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

// Spec for Option
#[flux_rs::extern_spec]
#[flux_rs::refined_by(b: bool)]
enum Option<T> {
    #[variant(Option<T>[false])]
    None,
    #[variant({T} -> Option<T>[true])]
    Some(T),
}

#[flux_rs::extern_spec]
impl<T> Option<T> {
    #[sig(fn(&Option<T>[@b]) -> bool[b])]
    const fn is_some(&self) -> bool;

    #[sig(fn(&Option<T>[@b]) -> bool[!b])]
    const fn is_none(&self) -> bool;
}

// Spec for slice
#[flux_rs::extern_spec]
impl<T> [T] {
    #[flux_rs::sig(fn(&[T][@n]) -> usize[n])]
    fn len(v: &[T]) -> usize;

    #[flux_rs::sig(fn(&[T][@n]) -> Iter<T>[0, n])]
    fn iter(v: &[T]) -> Iter<'_, T>;
}

// Specs for std::slice::Iter and Enumerate
#[flux_rs::extern_spec(std::slice)]
#[flux_rs::refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::refined_by(idx: int, inner: I)]
struct Enumerate<I>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::generics(Self as base)]
#[flux_rs::assoc(fn done(self: Self) -> bool )]
#[flux_rs::assoc(fn step(self: Self, other: Self) -> bool )]
trait Iterator {
    #[flux_rs::sig(fn(self: &strg Self[@curr_s]) -> Option<Self::Item>[!<Self as Iterator>::done(curr_s)] ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<Self::Item>;

    #[flux_rs::sig(fn(Self[@s]) -> Enumerate<Self>[0, s])]
    fn enumerate(self) -> Enumerate<Self> where Self: Sized;
}

#[flux_rs::extern_spec(std::slice)]
#[flux::generics(T as base)]
#[flux::assoc(fn done(x: Iter<T>) -> bool { x.idx >= x.len })]
#[flux::assoc(fn step(x: Iter<T>, y: Iter<T>) -> bool { x.idx + 1 == y.idx && x.len == y.len})]
impl<'a, T> Iterator for Iter<'a, T> {
    #[flux_rs::sig(fn(self: &strg Iter<T>[@curr_s]) -> Option<_>[curr_s.idx < curr_s.len] ensures self: Iter<T>{next_s: curr_s.idx + 1 == next_s.idx && curr_s.len == next_s.len})]
    fn next(&mut self) -> Option<&'a T>;
}

#[flux_rs::extern_spec(std::iter)]
#[flux::generics(I as base)]
#[flux::assoc(fn done(x: Enumerate<I>) -> bool { <I as Iterator>::done(x.inner)})]
#[flux::assoc(fn step(x: Enumerate<I>, y: Enumerate<I>) -> bool { <I as Iterator>::step(x.inner, y.inner)})]
impl<I: Iterator> Iterator for Enumerate<I> {
    #[flux_rs::sig(fn(self: &strg Enumerate<I>[@curr_s]) -> Option<(usize[curr_s.idx], _)>[!<I as Iterator>::done(curr_s.inner)] 
    ensures self: Enumerate<I>{next_s: curr_s.idx + 1 == next_s.idx && <I as Iterator>::step(curr_s.inner, next_s.inner)})]
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>;
}

// Tests
#[flux_rs::sig(fn(slice: &[u8]{n: n > 0}))]
fn test_iter1(slice: &[u8]){
    let mut iter = slice.iter();
    let next = iter.next();
    assert(next.is_some());
}

#[flux_rs::should_fail]
#[flux_rs::sig(fn(slice: &[u8]{n: n > 0}))]
fn test_iter1_neg(slice: &[u8]){
    assert(slice.len() > 0);
    let mut iter = slice.iter();
    let next = iter.next();
    assert(next.is_some());
    assert(iter.next().is_some());
}


#[flux_rs::sig(fn(slice: &[u8]{n: n > 1}))]
fn test_enumerate1(slice: &[u8]){
    assert(slice.len() > 0);
    let mut enumer = slice.iter().enumerate();

    let next = enumer.next();
    assert(next.is_some());
    let (idx,_) = next.unwrap();
    assert(idx == 0);

    let next_next = enumer.next();
    assert(next_next.is_some());
    let (idx,_) = next_next.unwrap();
    assert(idx == 1);
}

#[flux_rs::sig(fn(&[usize][1]) )]
pub fn test_enumer2(slice: &[usize]) {
    assert(slice.len() == 1);
    let mut enumer = slice.iter().enumerate();

    let next = enumer.next();
    assert(next.is_some());

    let next_next = enumer.next();
    assert(next_next.is_none())
}


#[flux_rs::sig(fn(&[usize][@n]) )]
pub fn test_enumer3(slice: &[usize]) {
    let mut e = slice.iter().enumerate();
    while let Some((idx,_)) = e.next(){
        assert(idx < slice.len())
    }
}