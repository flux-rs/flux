#![allow(dead_code)]

pub struct RVec<T> {
    inner: Vec<T>,
}

impl<T> RVec<T> {
    #[lr::assume]
    #[lr::ty(fn() -> RVec<T> @ 0)]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[lr::assume]
    #[lr::ty(fn<n: int>(self: RVec<T>@n; ref<self>, T) -> i32@0; self: RVec<T> @ {n + 1})]
    pub fn push(&mut self, item: T) -> i32 {
        self.inner.push(item);
        0
    }

    #[lr::assume]
    #[lr::ty(fn<n: int>(self: RVec<T>@n; ref<self>) -> usize@n; self: RVec<T>@n)]
    pub fn len(&mut self) -> usize {
        self.inner.len()
    }

    #[lr::assume]
    #[lr::ty(fn<len: int>(self: RVec<T>@len; ref<self>) -> bool@{len == 0}; self: RVec<T>@len)]
    pub fn is_empty(&mut self) -> bool {
        self.inner.is_empty()
    }

    #[lr::assume]
    #[lr::ty(
    fn<len:int>(self: RVec<T>@len; ref<self>, usize{v: 0 <= v && v < len}) -> &T; self: RVec<T>@len)
    ]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        &mut self.inner[i]
    }

    #[lr::assume]
    #[lr::ty(fn<len: int {len > 0}>(self: RVec<T>@len; ref<self>) -> T; self: RVec<T>@{len - 1})]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[lr::assume]
    #[lr::ty(
        fn<len: int>
        (self: RVec<T>@len; ref<self>, usize{v : 0 <= v && v < len}, usize{v : 0 <= v && v < len})
        ->
        i32@0; self: RVec<T>@len
    )]
    pub fn swap(&mut self, a: usize, b: usize) -> i32 {
        self.inner.swap(a, b);
        0
    }
}
