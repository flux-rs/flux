#![allow(dead_code)]

flux_rs::defs! {
    opaque sort VSeq<T>;
    fn vseq_empty<T>() -> VSeq<T>;
    fn vseq_singleton<T>(v: T) -> VSeq<T>;
    fn vseq_append<T>(s1: VSeq<T>, s2: VSeq<T>) -> VSeq<T>;
    fn vseq_get<T>(s1: VSeq<T>, pos: int) -> T;
    fn vseq_set<T>(s1: VSeq<T>, pos: int, val: T) -> VSeq<T>;
    fn vseq_slice<T>(s1: VSeq<T>, left: int, right: int) -> VSeq<T>;
    fn vseq_len<T>(s1: VSeq<T>) -> int;
    fn iseq_push(s1: VSeq<int>, e: int) -> VSeq<int> {
        vseq_append(s1, vseq_singleton(e))
    }
    fn iseq_pop(s1: VSeq<int>) -> int {
        vseq_get(s1, vseq_len(s1) - 1)
    }
}

#[flux::opaque]
#[flux::refined_by(elems: VSeq<T>)]
pub struct SVec<T> {
    inner: Vec<T>,
}

impl<T> SVec<T> {

    #[flux::trusted]
    #[flux::sig(fn() -> SVec<T>[vseq_empty()])]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &mut Self[@elems], T[@item]) ensures self : Self[vseq_append(elems, vseq_singleton(item))])]
    pub fn push(&mut self, item: T) {
        self.inner.push(item);
    }

    #[flux::trusted]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[flux::trusted]
    #[flux::sig(fn(&Self[@elems]) -> bool[elems == vseq_empty()] ensures vseq_len(elems) == 0)]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[flux::trusted]
    #[flux::sig(fn(&Self[@elems], pos: usize{ 0 <= pos && pos < vseq_len(elems) }) -> &T[vseq_get(elems, pos)])]
    pub fn get(&self, i: usize) -> &T {
        &self.inner[i]
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &mut Self[@elems]) -> T[vseq_get(elems, vseq_len(elems) - 1)]
        requires vseq_len(elems) > 0
        ensures self : Self[vseq_slice(elems, 0, vseq_len(elems) - 1)]
    )]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[flux::trusted]
    #[flux::sig(fn(self: &mut Self[@elems], usize[@a], usize[@b]) ensures self : Self[vseq_set(vseq_set(elems, b, vseq_get(elems, a)), a, vseq_get(elems, b))])]
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
