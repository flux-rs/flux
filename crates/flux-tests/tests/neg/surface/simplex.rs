#![allow(unused_attributes)]
#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rmat.rs"]
pub mod rmat;
use rmat::RMat;

/* step 1 */

#[flux::sig(fn(&RMat<f32>[m,n], m: usize{0 < m}, n: usize{0 < n}) -> bool)]
pub fn is_neg(arr2: &RMat<f32>, _m: usize, n: usize) -> bool {
    let mut j = 1;
    while j < n - 1 {
        if *arr2.get(0, j) < 0.0 {
            return true;
        }
        j += 1;
    }
    false
}

/* step 2 */

#[flux::sig(fn(m: usize{0 < m}, n: usize{0 < n}, &RMat<f32>[m, n]) -> bool)]
pub fn unb1(m: usize, n: usize, arr2: &RMat<f32>) -> bool {
    let mut i = 0;
    let mut j = 1;

    // INV: 0 < i <= m, 0 <= j < n
    while j < n - 1 {
        if *arr2.get(0, j) < 0.0 {
            i = i + 1;
            loop {
                if i < m {
                    if *arr2.get(i, j) < 0.0 {
                        i = i + 1
                    } else {
                        i = 0;
                        j = j + 1;
                        break;
                    }
                } else {
                    return true;
                }
            }
        } else {
            i = 0;
            j = j + 1;
        }
    }
    false
}

/* step 3 */

#[flux::sig(fn(m: usize{0 < m}, n: usize{2 < n}, &RMat<f32>[m,n]) -> usize{v: 0 < v && v+1 < n})]
pub fn enter_var(_m: usize, n: usize, arr2: &RMat<f32>) -> usize {
    let mut c = *arr2.get(0, 1);
    let mut j = 1;
    let mut j_ = 2;
    while j_ < n - 1 {
        // INV j+1 < n, j_ < n
        let c_ = *arr2.get(0, j_);
        if c_ < c {
            j = j_;
            c = c_;
        }
        j_ += 1
    }
    j
}

/* step 4 */

#[flux::sig(fn(m: usize, n: usize, &RMat<f32>[m, n], j: usize{0 < j && j < n}, i0: usize{0 < i0 && i0 < m}, f32) -> usize{v: 0 < v && v < m})]
pub fn depart_var(m: usize, n: usize, arr2: &RMat<f32>, j: usize, i0: usize, r0: f32) -> usize {
    let mut i = i0;
    let mut r = r0;
    let mut i_ = i + 1;
    while i_ < m {
        let c_ = *arr2.get(i_, j);
        if 0.0 < c_ {
            let r_ = *arr2.get(i_, n - 1) / c_;
            if r_ < r {
                i = i_;
                r = r_;
            }
            i_ += 1;
        } else {
            i_ += 1
        }
    }
    i
}

#[flux::sig(fn(m: usize{0 < m}, n: usize{0 < n}, &RMat<f32>[m, n], j: usize{0 < j && j < n}) -> usize{v:0 < v && v < m})]
pub fn init_ratio_i(m: usize, _n: usize, arr2: &RMat<f32>, j: usize) -> usize {
    let mut i = 1;
    while i < m {
        let c = *arr2.get(i, j);
        if 0.0 < c {
            return i;
        }
        i += 1;
    }
    rmat::die() // abort ("init_ratio: negative coefficients!")
}

#[flux::sig(fn(m: usize{0 < m}, n: usize{0 < n}, &RMat<f32>[m, n],
             j: usize{0 < j && j < n}, i:usize{0 < i && i < m}
            ) -> f32)]
pub fn init_ratio_c(_m: usize, n: usize, arr2: &RMat<f32>, j: usize, i: usize) -> f32 {
    *arr2.get(i, j) / *arr2.get(i, n - 1)
}

/* step 5 */

#[flux::sig(fn(m: usize, n: usize, &mut RMat<f32>[m,n], i: usize{0 < i && i < m}, j: usize{0 < j && j < n}) -> i32)]
fn row_op(m: usize, n: usize, arr2: &mut RMat<f32>, i: usize, j: usize) -> i32 {
    // norm(m, n, arr2, i, j);
    let c = *arr2.get(i, j);
    let mut j = 1;
    while j < n {
        *arr2.get_mut(i, j) /= c;
        j += 1;
    }

    // ro_op_aux3(m, n, arr2, i, j, 0)
    let mut i_ = 0;
    while i_ < m {
        if i_ != i {
            let c_ = *arr2.get(i_, j); //~ ERROR refinement type error
            let mut j = 1;
            while j < n {
                let cj = *arr2.get(i, j);
                let cj_ = *arr2.get(i_, j);
                *arr2.get_mut(i_, j) = cj_ - cj * c_;
                j += 1
            }
        }
        i_ += 1
    }
    0
}

#[flux::sig(fn(m: usize{1 < m}, n: usize{2 < n}, &mut RMat<f32>[m, n]) -> i32)]
pub fn simplex(m: usize, n: usize, arr2: &mut RMat<f32>) -> i32 {
    while is_neg(arr2, m, n) {
        if unb1(m, n, arr2) {
            rmat::die();
            return 0;
        } else {
            let j = enter_var(m, n, arr2);
            let i = init_ratio_i(m, n, arr2, j);
            let r = init_ratio_c(m, n, arr2, j, i);
            let i = depart_var(m, n, arr2, j, i, r);
            row_op(m, n, arr2, i, j);
        }
    }
    0
}
