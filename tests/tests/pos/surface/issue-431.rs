#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn(vec: &mut RVec<_>[100]))]
pub fn test(vec: &mut RVec<RVec<i32>>) {
    vec[0] = RVec::new();
}

#[flux::sig(fn(&RVec<f32>[@n], usize) -> RVec<f32>[n])]
fn normal(x: &RVec<f32>, w: usize) -> RVec<f32> {
    let mut i = 0;
    let mut res = RVec::new();
    while i < x.len() {
        res.push(x[i] / (w as f32));
        i += 1;
    }
    res
}

#[flux::sig(fn (n: usize, centers: &mut RVec<RVec<f32>[n]>[@k], new_centers: RVec<(usize{v: v < k}, (RVec<f32>[n], usize))>))]
pub fn update_centers(
    _n: usize,
    centers: &mut RVec<RVec<f32>>,
    new_centers: RVec<(usize, (RVec<f32>, usize))>,
) {
    for (i, (x, size)) in new_centers {
        centers[i] = normal(&x, size)
    }
}
