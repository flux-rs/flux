#![allow(unused_attributes)]
#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
pub mod rvec;
use rvec::RVec;

/// distance between two points
#[flux::sig(fn(&RVec<f32>[@n], &RVec<f32>[n]) -> f32)]
fn dist(x: &RVec<f32>, y: &RVec<f32>) -> f32 {
    let mut res = 0.0;
    let mut i = 0;
    while i < x.len() {
        let di = x[i] - y[i];
        res += di * di;
        i += 1;
    }
    res
}

/// adding two points (updates the first)
#[flux::sig(fn(&mut RVec<f32>[@n], &RVec<f32>[n]) -> i32)]
fn add(x: &mut RVec<f32>, y: &RVec<f32>) -> i32 {
    let mut i = 0;
    let n = x.len();
    while i < n {
        let xi = x[i];
        let yi = y[i];
        x[i] = xi + yi;
        i += 1;
    }
    0
}

/// normalizing a point (cluster) by size
#[flux::sig(fn(&mut RVec<f32>[@n], usize) -> i32)]
fn normal(x: &mut RVec<f32>, w: usize) -> i32 {
    let mut i = 0;
    while i < x.len() {
        let xi = x[i];
        x[i] = xi / (w as f32);
        i += 1;
    }
    0
}

/// creating (empty) 0-center for each cluster
#[flux::sig(fn(n: usize, k: usize{0 < k}) -> RVec<RVec<f32>[n]>[k])]
fn init_centers(n: usize, k: usize) -> RVec<RVec<f32>> {
    let mut res = RVec::new();
    let mut i = 0;
    while i <= k {
        res.push(RVec::from_elem_n(0.0, n));
        i += 1;
    }
    res //~ ERROR postcondition might not hold
}

/// finding the nearest center to a point
#[flux::sig(fn(&RVec<f32>[@n], &RVec<RVec<f32>[n]>[@k]) -> usize{v: v < k}
              requires 0 < k)]
fn nearest(p: &RVec<f32>, cs: &RVec<RVec<f32>>) -> usize {
    // let n = p.len();
    let k = cs.len();
    let mut res = 0;
    let mut min = f32::MAX;
    let mut i = 0;
    while i < k {
        let di = dist(&cs[i], p);
        if di < min {
            res = i;
            min = di;
        }
        i += 1;
    }
    res
}

// TODO: the `n` is not needed, except to prevent a silly parse error!
#[flux::sig(fn(n: usize, &mut RVec<RVec<f32>[n]>[@k], &RVec<usize>[k]) -> i32)]
fn normalize_centers(_n: usize, cs: &mut RVec<RVec<f32>>, weights: &RVec<usize>) -> i32 {
    let k = cs.len();
    let mut i = 0;
    while i < k {
        normal(&mut cs[i], weights[i]);
        i += 1;
    }
    0
}

/// updating the centers
#[flux::sig(fn(n: usize, k: RVec<RVec<f32>[n]>{0 < k}, &RVec<RVec<f32>[n]>) -> RVec<RVec<f32>[n]>[k])]
fn kmeans_step(n: usize, cs: RVec<RVec<f32>>, ps: &RVec<RVec<f32>>) -> RVec<RVec<f32>> {
    let k = cs.len();

    let mut res_points = init_centers(n, k);

    let mut res_size = RVec::from_elem_n(0, k);

    let mut i = 0;
    while i < ps.len() {
        let j = nearest(&ps[i], &cs);
        add(&mut res_points[j], &ps[i]);
        res_size[j] += 1;
        i += 1;
    }

    normalize_centers(n, &mut res_points, &res_size);

    res_points
}

/// kmeans: iterating the center-update-steps
#[flux::sig(fn(n: usize, k: RVec<RVec<f32>[n]>, &RVec<RVec<f32>[n]>, i32) -> RVec<RVec<f32>[n]>[k])]
pub fn kmeans(n: usize, cs: RVec<RVec<f32>>, ps: &RVec<RVec<f32>>, iters: i32) -> RVec<RVec<f32>> {
    let mut i = 0;
    let mut res = cs;
    while i < iters {
        res = kmeans_step(n, res, ps); //~ ERROR precondition might not hold
        i += 1;
    }
    res
}
