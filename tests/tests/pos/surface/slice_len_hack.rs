use flux_rs::attrs::*;

pub fn silly_slice(_src: &mut [i32]) -> usize {
    12
}

pub fn mickey(n: usize) -> usize {
    n + 1
}

#[spec(fn(src: &mut [i32][12]))]
pub fn blob(src: &mut [i32]) {
    let _k = silly_slice(src);
    let _n = mickey(5);
}
