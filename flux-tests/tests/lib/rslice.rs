use std::marker::PhantomData;

use super::RVec;

#[flux::opaque]
#[flux::refined_by(len: int, valid: (int, int) -> bool)]
pub struct RSlice<'a, T> {
    data: *mut T,
    len: usize,
    _marker: PhantomData<&'a mut [T]>,
}

impl<'a, T> RSlice<'a, T> {
    #[flux::trusted]
    #[flux::sig(fn(vec: &mut RVec<T>[@n]) -> RSlice<T>[n, |i,j| true])]
    pub fn from_vec(vec: &mut RVec<T>) -> RSlice<T> {
        RSlice::from_slice(vec.as_mut_slice())
    }

    #[flux::trusted]
    #[flux::sig(fn(slice: &mut [T][@n]) -> RSlice<T>[n, |i,j| true])]
    pub fn from_slice(slice: &mut [T]) -> RSlice<T> {
        RSlice { data: slice.as_mut_ptr(), len: slice.len(), _marker: PhantomData }
    }

    #[flux::trusted]
    #[flux::sig(
        fn(self: &strg RSlice<T>[@len, @valid], left: usize, right: usize) -> RSlice<T>[right - left + 1, |i,j| true]
        requires left <= right && right < len && valid(left, right)
        ensures self: RSlice<T>[len, |i, j| valid(i, j) && (right < i || j < left)]
    )]
    pub fn subslice(&mut self, left: usize, right: usize) -> RSlice<'a, T> {
        unsafe { RSlice { data: self.data.add(left), len: right - left + 1, _marker: PhantomData } }
    }

    #[flux::trusted]
    #[flux::sig(fn(&mut RSlice<T>[@n, |i,j| true]) -> &mut [T][n])]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.data, self.len) }
    }

    #[flux::trusted]
    #[flux::sig(fn(&RSlice<T>[@n, |i,j| true]) -> &[T][n])]
    pub fn as_slice(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.data, self.len) }
    }
}
