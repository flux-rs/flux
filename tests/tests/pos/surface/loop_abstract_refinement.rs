#![flux::cfg(scrape_quals = true)]
#![flux::defs {
    qualifier MyQ1(k: int, i: int, j: int, n: int) {
        (0 <= k && k < i) || (j <= k && k < n)
    }
}]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::opaque]
#[flux::refined_by(available: int -> bool)]
pub struct VecBorrows<'a, T> {
    ptr: *mut T,
    _marker: std::marker::PhantomData<&'a mut [T]>,
}

impl<T> RVec<T> {
    #[flux::trusted]
    #[flux::sig(fn(self: &mut Self[@len]) -> VecBorrows<T>[|i| 0 <= i && i < len])]
    pub fn borrows(self: &mut Self) -> VecBorrows<T> {
        VecBorrows { ptr: self.as_mut_slice().as_mut_ptr(), _marker: std::marker::PhantomData }
    }
}

impl<'a, T> VecBorrows<'a, T> {
    #[flux::trusted]
    #[flux::sig(
        fn(self: &strg Self[@available], idx: usize{available(idx)}) -> &mut T
        ensures self: Self[|i| available(i) && i != idx]
    )]
    pub fn get(&mut self, idx: usize) -> &'a mut T {
        unsafe { &mut *self.ptr.add(idx) }
    }
}

pub struct Particle;

impl Particle {
    fn collision(&mut self, _other: &mut Self) {}
}

#[flux::sig(fn(&mut RVec<Particle>[@len]))]
fn foo(vec: &mut RVec<Particle>) {
    let mut i = 0;
    let n = vec.len();
    while i < n {
        let mut j = i + 1;
        let mut idx = vec.borrows();
        let a = idx.get(i);
        while j < n {
            let b = idx.get(j);
            a.collision(b);
            j += 1;
        }
        i += 1;
    }
}
