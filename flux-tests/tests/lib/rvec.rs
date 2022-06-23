#![allow(dead_code)]

#[flux::opaque]
#[flux::refined_by(len: int)]
pub struct RVec<T> {
    inner: Vec<T>,
}

impl<T> RVec<T> {
    #[flux::assume]
    #[flux::ty(fn() -> RVec<T> @ 0)]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[flux::assume]
    #[flux::ty(fn<n: int>(self: RVec<T>@n; ref<self>, T) -> i32@0; self: RVec<T> @ {n + 1})]
    pub fn push(&mut self, item: T) -> i32 {
        self.inner.push(item);
        0
    }

    #[flux::assume]
    #[flux::ty(fn<len: int>(&RVec<T>@len) -> usize@len)]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[flux::assume]
    #[flux::ty(fn<len: int>(&RVec<T>@len) -> bool@{len == 0})]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[flux::assume]
    #[flux::ty(fn<len:int>(&RVec<T>@len, usize{v: 0 <= v && v < len}) -> &T)]
    pub fn get(&self, i: usize) -> &T {
        &self.inner[i]
    }

    #[flux::assume]
    #[flux::ty(fn<len:int>(&weak RVec<T>@len, usize{v: 0 <= v && v < len}) -> &weak T)]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        &mut self.inner[i]
    }

    #[flux::assume]
    #[flux::ty(fn<len: int {len > 0}>(self: RVec<T>@len; ref<self>) -> T; self: RVec<T>@{len - 1})]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[flux::assume]
    #[flux::ty(
        fn<len: int>
        (self: RVec<T>@len; ref<self>, usize{v : 0 <= v && v < len}, usize{v : 0 <= v && v < len})
        ->
        i32@0; self: RVec<T>@len
    )]
    pub fn swap(&mut self, a: usize, b: usize) -> i32 {
        self.inner.swap(a, b);
        0
    }

    #[flux::assume]
    #[flux::ty(fn<len: int>(T, usize @ len) -> RVec<T>@len)]
    pub fn from_elem_n(elem: T, n: usize) -> Self
    where
        T: Copy,
    {
        let mut vec = Self::new();
        let mut i = 0;
        while i < n {
            vec.push(elem);
            i += 1;
        }
        vec
    }
}
