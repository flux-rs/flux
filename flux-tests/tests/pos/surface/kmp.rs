#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(
    fn(&RVec<u8>[@len]) -> RVec<usize{v: v < len}>[len]
    requires len > 0
)]
fn kmp_table(p: &RVec<u8>) -> RVec<usize> {
    let m = p.len();
    let mut t = RVec::from_elem_n(0, m);

    let mut i = 1;
    let mut j = 0;
    while i < m {
        if p[i] == p[j] {
            t[i] = j + 1;
            i = i + 1;
            j = j + 1;
        } else if j == 0 {
            t[i] = 0;
            i = i + 1;
        } else {
            j = t[j - 1];
        }
    }
    t
}

#[flux::sig(fn(m: RVec<u8>{0 < m && m <= n}, &RVec<u8>[@n]) -> usize)]
pub fn kmp_search(mut pat: RVec<u8>, target: &RVec<u8>) -> usize {
    let mut t_i = 0;
    let mut p_i = 0;
    let mut result_idx = 0;

    let t = kmp_table(&mut pat);

    while t_i < target.len() && p_i < pat.len() {
        if target[t_i] == pat[p_i] {
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
                p_i = t[p_i - 1];
            }
            t_i = t_i + 1;
            result_idx = 0;
        }
    }
    target.len()
}
