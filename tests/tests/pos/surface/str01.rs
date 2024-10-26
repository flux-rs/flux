#![allow(dead_code)]

pub fn str01() -> usize {
    let x = "str";
    x.len()
}

#[flux::sig(fn (&str["cat"]))]
fn require_cat(_x: &str) {}

pub fn test_cat() {
    require_cat("cat");
    // require_cat("dog"); //~ ERROR refinement type
}

#[flux::sig(fn (&str[@a], &{str[@b] | a == b}))]
fn require_eq(_x: &str, _y: &str) {}

pub fn test_eq() {
    require_eq("a", "a");
    // require_eq("a", "b"); //~ ERROR refinement type
}
pub fn panic() {
    panic!("a panic")
}


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
    // x.len() //~ ERROR refinement type
}
