#![allow(dead_code)]

use flux_rs::extern_spec;

#[extern_spec]
impl str {
    #[flux::sig(fn(&str[@s]) -> usize[str_len(s)])]
    fn len(s: &str) -> usize;
}

#[flux::sig(fn() -> usize[3])]
pub fn str_len_good() -> usize {
    let x = "hog";
    x.len()
}

#[flux::sig(fn() -> usize[3])]
pub fn str_len_bad() -> usize {
    let x = "piglet";
    x.len() //~ ERROR refinement type
}
