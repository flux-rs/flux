#![allow(dead_code)]

flux_rs::defs! {
    opaque sort ISeq;
    fn iseq_empty() -> ISeq;
    fn iseq_singleton(v: int) -> ISeq;
    fn iseq_append(s1: ISeq, s2: ISeq) -> ISeq;
    fn iseq_get(s1: ISeq, pos: int) -> int;
    fn iseq_set(s1: ISeq, pos: int, val: int) -> ISeq;
    fn iseq_slice(s1: ISeq, left: int, right: int) -> ISeq;
    fn iseq_len(s1: ISeq) -> int;
    fn iseq_push(s1: ISeq, e: int) -> ISeq {
        iseq_append(s1, iseq_singleton(e))
    }
    fn iseq_pop(s1: ISeq) -> int {
        iseq_get(s1, iseq_len(s1) - 1)
    }
}

#[flux::opaque]
#[flux::refined_by(elems: ISeq)]
pub struct SVec {
    inner: Vec<i32>,
}

impl SVec {

    #[flux::trusted]
    #[flux::sig(fn() -> SVec[iseq_empty()] ensures iseq_len(iseq_empty()) == 0)]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &mut Self[@elems], i32[@item]) ensures self : Self[iseq_append(elems, iseq_singleton(item))])]
    pub fn push(&mut self, item: i32) {
        self.inner.push(item);
    }

    #[flux::trusted]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[flux::trusted]
    #[flux::sig(fn(&Self[@elems]) -> bool[elems == iseq_empty()] ensures iseq_len(elems) == 0)]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[flux::trusted]
    #[flux::sig(fn(&Self[@elems], usize[@pos]) -> &i32[iseq_get(elems, pos)])]
    pub fn get(&self, i: usize) -> &i32 {
        &self.inner[i]
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &mut Self[@elems]) -> i32[iseq_get(elems, iseq_len(elems) - 1)] ensures self : Self[iseq_slice(elems, 0, iseq_len(elems) - 1)])]
    pub fn pop(&mut self) -> i32 {
        self.inner.pop().unwrap()
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &mut Self[@elems], usize[@a], usize[@b]) ensures self : Self[iseq_set(iseq_set(elems, b, iseq_get(elems, a)), a, iseq_get(elems, b))])]
    pub fn swap(&mut self, a: usize, b: usize) {
        self.inner.swap(a, b);
    }

    // pub fn as_mut_slice(&mut self) -> &mut [T] {
    //     self.inner.as_mut_slice()
    // }

    // pub fn from_array<const N: usize>(arr: [T; N]) -> Self {
    //     Self { inner: Vec::from(arr) }
    // }

    // pub fn from_slice(xs: &[T]) -> Self
    // where
    //     T: Clone,
    // {
    //     Self { inner: Vec::from(xs) }
    // }

    // pub fn from_elem_n(elem: T, n: usize) -> Self
    // where
    //     T: Copy,
    // {
    //     let mut vec = Self::new();
    //     let mut i = 0;
    //     while i < n {
    //         vec.push(elem);
    //         i += 1;
    //     }
    //     vec
    // }

    // pub fn clone(&self) -> Self
    // where
    //     T: Clone,
    // {
    //     Self { inner: self.inner.clone() }
    // }

    // pub fn extend_from_slice(&mut self, other: &[T])
    // where
    //     T: Clone,
    // {
    //     self.inner.extend_from_slice(other)
    // }

    // pub fn map<U, F>(&self, f: F) -> RVec<U>
    // where
    //     F: Fn(&T) -> U,
    // {
    //     RVec { inner: self.inner.iter().map(f).collect() }
    // }

    // pub fn fold<B, F>(&self, init: B, f: F) -> B
    // where
    //     F: FnMut(B, &T) -> B,
    // {
    //     self.inner.iter().fold(init, f)
    // }
}

// #[flux::opaque]
// pub struct RVecIter<T> {
//     vec: RVec<T>,
//     curr: usize,
// }

// impl<T> IntoIterator for RVec<T> {
//     type Item = T;
//     type IntoIter = RVecIter<T>;

//     // TODO: cannot get variant of opaque struct
//     #[flux::trusted]
//     #[flux::sig(fn(RVec<T>) -> RVecIter<T>)]
//     fn into_iter(self) -> RVecIter<T> {
//         RVecIter { vec: self, curr: 0 }
//     }
// }

// impl<T> Iterator for RVecIter<T> {
//     type Item = T;

//     // TODO: cannot get variant of opaque struct
//     #[flux::trusted]
//     #[flux::sig(fn(&mut RVecIter<T>) -> Option<T>)]
//     fn next(&mut self) -> Option<T> {
//         self.vec.inner.pop()
//     }
// }

// impl<T> std::ops::Index<usize> for RVec<T> {
//     type Output = T;

//     #[flux::trusted_impl]
//     #[flux::sig(fn(&RVec<T>[@n], usize{v : v < n}) -> &T)]
//     fn index(&self, index: usize) -> &T {
//         self.get(index)
//     }
// }

// impl<T> std::ops::IndexMut<usize> for RVec<T> {
//     #[flux::trusted_impl]
//     #[flux::sig(fn(&mut RVec<T>[@n], usize{v : v < n}) -> &mut T)]
//     fn index_mut(&mut self, index: usize) -> &mut T {
//         self.get_mut(index)
//     }
// }
