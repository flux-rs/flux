#![feature(register_tool)]
#![register_tool(lr)]

mod rvec;
use rvec::RVec;

#[lr::ty(fn<len: int{len > 0}>(vec: RVec<u8>@len; ref<vec>) -> RVec<usize{v: v >=0 && v <= len}>@len)]
fn kmp_table(p: &mut RVec<u8>) -> RVec<usize> {
    let m = p.len();
    let mut t = RVec::from_elem_n(0, m);

    let mut i = 1;
    let mut j = 0;
    while i < m {
        let a = *p.get_mut(i);
        let b = *p.get_mut(j);
        if a == b {
            *t.get_mut(i) = j + 1;
            i = i + 1;
            j = j + 1;
        } else if j == 0 {
            *t.get_mut(i) = 0;
            i = i + 1;
        } else {
            j = *t.get_mut(j - 1);
        }
    }
    t
}

#[lr::ty(fn<n: int{0 < n}, m: int{0 < m && m <= n }>(target: RVec<u8>@n; RVec<u8>@m, ref<target>) -> usize)]
pub fn kmp_search(mut pat: RVec<u8>, target: &mut RVec<u8>) -> usize {
    let mut t_i = 0;
    let mut p_i = 0;
    let mut result_idx = 0;

    let mut t = kmp_table(&mut pat);

    while t_i < target.len() && p_i < pat.len() {
        if *target.get_mut(t_i) == *pat.get_mut(p_i) {
            if result_idx == 0 {
                result_idx = t_i;
            }
            t_i = t_i + 1;
            p_i = p_i + 1;
            if p_i >= pat.len() {
                return result_idx;
            }
        } else {
            if p_i == 0 {
                p_i = 0;
            } else {
                p_i = *t.get_mut(p_i - 1);
            }
            t_i = t_i + 1;
            result_idx = 0;
        }
    }
    target.len()
}
