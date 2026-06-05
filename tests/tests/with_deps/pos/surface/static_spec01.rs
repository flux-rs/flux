#![allow(unused)]

extern crate flux_core;

#[flux::sig(fn (xs: &[u32; _], idxs: &[u8{v: v < N}; _]) -> u32)]
pub fn lib<const N: usize, const M: usize>(xs: &[u32; N], idxs: &[u8; M]) -> u32 {
    if idxs.len() > 10 {
        let idx = idxs[0] as usize;
        xs[idx]
    } else {
        0
    }
}

mod goober {

    static XS: [u32; 5] = [1, 2, 3, 4, 5];

    #[flux::spec([u8{v: v < 5}; 3])]
    static IDXS: [u8; 3] = [0, 1, 2];

    fn test() {
        let result = super::lib(&XS, &IDXS);
    }
}
