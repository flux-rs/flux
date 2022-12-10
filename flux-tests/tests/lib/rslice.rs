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
    #[flux::assume]
    #[flux::sig(fn(vec: &mut RVec<T>[@n]) -> RSlice<T>[n, |i,j| true])]
    pub fn from_vec(vec: &'a mut RVec<T>) -> RSlice<T> {
        let inner = &mut vec.inner;
        RSlice { data: inner.as_mut_ptr(), len: inner.len(), _marker: PhantomData }
    }

    #[flux::assume]
    #[flux::sig(
        fn(self: &strg RSlice<T>[@len, @valid], left: usize, right: usize) -> RSlice<T>[right - left + 1, |i,j| true]
        requires left <= right && right < len && valid(left, right)
        ensures self: RSlice<T>[len, |i, j| valid(i, j) && (right < i || j < left)]
    )]
    pub fn subslice(&mut self, left: usize, right: usize) -> RSlice<'a, T> {
        unsafe { RSlice { data: self.data.add(left), len: right - left + 1, _marker: PhantomData } }
    }
}
