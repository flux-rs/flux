#![allow(unused)]
use std::slice::Iter;

extern crate flux_core;

#[flux_rs::extern_spec(std::slice)]
#[flux_rs::refined_by(idx: int, len: int)]
struct Iter<'a, T>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::refined_by(idx: int, inner: I)]
struct Enumerate<I>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::assoc(fn done(self: Self) -> bool  )]
#[flux_rs::assoc(fn step(self: Self, other: Self) -> bool )]
trait Iterator {
    #[flux_rs::sig(fn(self: &strg Self[@curr_s]) -> Option<Self::Item>[!<Self as Iterator>::done(curr_s)] ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<Self::Item>;

    #[flux_rs::sig(fn(Self[@s]) -> Enumerate<Self>[0, s])]
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized;
}

#[flux_rs::sig(fn (bool[true]))]
fn assert(_b: bool) {}

#[flux_rs::extern_spec]
#[flux_rs::assoc(fn done(x: Iter) -> bool { x.idx >= x.len })]
#[flux_rs::assoc(fn step(x: Iter, y: Iter) -> bool { x.idx + 1 == y.idx && x.len == y.len})]
impl<'a, T> Iterator for Iter<'a, T> {
    #[flux_rs::sig(fn(self: &strg Iter<T>[@curr_s]) -> Option<_>[curr_s.idx < curr_s.len] ensures self: Iter<T>{next_s: curr_s.idx + 1 == next_s.idx && curr_s.len == next_s.len})]
    fn next(&mut self) -> Option<&'a T>;
}

// Helper functions for inspecting indexes of `Iter`
#[flux_rs::trusted]
#[flux_rs::sig(fn(&Iter<T>[@idx, @len]) -> usize[len])]
fn get_iter_len<'a, T>(iter: &Iter<'a, T>) -> usize {
    unimplemented!()
}

#[flux_rs::trusted]
#[flux_rs::sig(fn(&Iter<T>[@idx, @len]) -> usize[idx])]
fn get_iter_idx<'a, T>(iter: &Iter<'a, T>) -> usize {
    unimplemented!()
}

#[flux_rs::sig(fn(slice: &[u8]{n: n > 5}))]
fn test_iter1(slice: &[u8]) {
    let mut zebra = slice.iter();

    let iter_len0 = get_iter_len(&zebra);

    zebra.next();
    zebra.next();
    zebra.next();

    let iter_len1 = get_iter_len(&zebra);
    assert(iter_len0 == iter_len1);
    assert(iter_len1 > 0);

    let zz = zebra.next();
    assert(zz.is_some());

    let idx = get_iter_idx(&zebra);
    assert(idx == 4);
}

#[flux_rs::sig(fn(slice: &[u8][@n]) -> usize{r: n == r })]
fn test_iter4(slice: &[u8]) -> usize {
    let mut ctr = 0_usize;
    let mut iter = slice.iter();
    while let Some(_) = iter.next() {
        assert(ctr < slice.len());
        ctr += 1;
    }
    ctr
}

#[flux_rs::sig(fn(slice: &[u8]{n: n > 0}))]
fn test_iter1_neg(slice: &[u8]) {
    assert(slice.len() > 0);
    let mut iter = slice.iter();
    let next = iter.next();
    assert(next.is_some());
    assert(iter.next().is_some()); //~ ERROR: refinement type
}

#[flux_rs::extern_spec(std::iter)]
#[flux::assoc(fn done(x: Enumerate<I>) -> bool { <I as Iterator>::done(x.inner)})]
#[flux::assoc(fn step(x: Enumerate<I>, y: Enumerate<I>) -> bool { <I as Iterator>::step(x.inner, y.inner)})]
impl<I: Iterator> Iterator for Enumerate<I> {
    #[flux_rs::sig(fn(self: &strg Enumerate<I>[@curr_s]) -> Option<(usize[curr_s.idx], _)>[!<I as Iterator>::done(curr_s.inner)]
    ensures self: Enumerate<I>{next_s: curr_s.idx + 1 == next_s.idx && <I as Iterator>::step(curr_s.inner, next_s.inner)})]
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>;
}

#[flux_rs::sig(fn(slice: &[u8]{n: n > 1}))]
fn test_enumerate1(slice: &[u8]) {
    assert(slice.len() > 0);
    let mut enumer = slice.iter().enumerate();

    let next = enumer.next();
    assert(next.is_some());
    let (idx, _) = next.unwrap();
    assert(idx == 0);

    let next_next = enumer.next();
    assert(next_next.is_some());
    let (idx, _) = next_next.unwrap();
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
    while let Some((idx, _)) = e.next() {
        assert(idx < slice.len())
    }
}

#[flux_rs::sig(fn(&[usize][@len]) -> Option<usize{r: r < len}> )]
pub fn find_index_of_3(slice: &[usize]) -> Option<usize> {
    let mut e = slice.iter().enumerate();
    while let Some((idx, num)) = e.next() {
        if num == &3 {
            return Some(idx);
        }
    }
    None
}

// TODO: implement IntoIter so I can use these with `for` loops
