#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

/// A statically sized matrix represented with a linear vector
struct Matrix<const N: usize, const M: usize> {
    #[flux::field(RVec<i32>[N * M])]
    inner: RVec<i32>,
}

impl<const N: usize, const M: usize> Matrix<N, M> {
    fn new() -> Matrix<N, M> {
        Matrix { inner: RVec::from_elem_n(0, N * M) }
    }

    #[flux::sig(fn(&mut Self, i: usize, j: usize{ j < M }, v: i32))]
    fn set(&mut self, i: usize, j: usize, v: i32) {
        self.inner[i * M + j] = v //~ ERROR refinement type error
    }

    #[flux::sig(fn(&Self, i: usize{ i < N}, j: usize) -> i32)]
    fn get(&self, i: usize, j: usize) -> i32 {
        self.inner[i * M + j] //~ ERROR refinement type error
    }
}
