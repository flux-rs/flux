#![allow(dead_code)]

#[lr::opaque]
#[lr::refined_by(len: int)]
pub struct RVec<T> {
    inner: Vec<T>,
}

impl<T> RVec<T> {
    #[lr::assume]
    #[lr::sig(fn() -> RVec<T>{v:v==0)]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[lr::assume]
    #[lr::sig(fn(self: &mut n@RVec<T>, T) -> i32{v:v == 0}; self: RVec<T>{v:v == n+1})]
    pub fn push(&mut self, item: T) -> i32 {
        self.inner.push(item);
        0
    }

    #[lr::assume]
    #[lr::sig(fn(self: & n@RVec<T>) -> usize{v:v == n})]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[lr::assume]
    #[lr::sig(fn(self: & n@RVec<T>) -> bool{b: b == (len == 0)})]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[lr::assume]
    #[lr::sig(fn(self:& len@RVec<T>, usize{v: 0 <= v && v < len}) -> &T)]
    pub fn get(&self, i: usize) -> &T {
        &self.inner[i]
    }

    #[lr::assume]
    #[lr::sig(fn(self: &mut n@RVec<T>, usize{v: 0 <= v && v < n}) -> &weak T; self: RVec<T>{v:v == n})]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        &mut self.inner[i]
    }

    #[lr::assume]
    #[lr::sig(fn(self: &mut n@RVec<T>{0 < n}) -> T; self: RVec<T>{v: v == n - 1})]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[lr::assume]
    #[lr::sig(fn(self: &mut len@RVec<T>, a:usize{0 <= a && a < len}, b:usize{0 <= b && b < len})
              -> i32{v:v==0}; self: RVec<T>{v:v == len})]
    pub fn swap(&mut self, a: usize, b: usize) -> i32 {
        self.inner.swap(a, b);
        0
    }

    #[lr::assume]
    #[lr::sig(fn(elem:T, n:usize) -> RVec<T>{v:v==n})]
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
