#[path = "../../lib/rvec.rs"]
pub mod rvec;

use rvec::RVec;

#[flux::refined_by(rows: int, cols: int)]
pub struct RMat {
    #[flux::field(usize[cols])]
    cols: usize,
    #[flux::field(RVec<RVec<f32>[cols]>[rows])]
    inner: RVec<RVec<f32>>,
}

impl RMat {
    #[flux::sig(fn(rows: usize, cols: usize, f32) -> RMat[rows, cols])]
    pub fn new(rows: usize, cols: usize, elem: f32) -> RMat {
        let mut inner = RVec::new();
        let mut i = 0;
        while i <= rows {
            let r = RVec::from_elem_n(elem, cols);
            inner.push(r);
            i += 1;
        }
        Self { cols, inner }
    } //~ ERROR refinement type error

    #[flux::sig(fn() -> RMat[10, 300])]
    pub fn empty() -> RMat {
        Self { cols: 10, inner: RVec::new() }
        //~^ ERROR refinement type error
        //~^^ ERROR refinement type error
    }

    #[flux::sig(fn(&RMat[@m, @n], usize{v: v < m}, usize{v: v < n}) -> &f32)]
    pub fn get(&self, i: usize, j: usize) -> &f32 {
        &self.inner.get(i).get(j + 1) //~ ERROR refinement type error
    }

    #[flux::sig(fn(&mut RMat[@m, @n], usize{v: v < m}, usize{v: v < n}) -> &mut f32)]
    pub fn get_mut(&mut self, i: usize, j: usize) -> &mut f32 {
        self.inner.get_mut(i + 1).get_mut(j) //~ ERROR refinement type error
    }
}
