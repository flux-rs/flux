#![allow(dead_code)]

use flux_rs::extern_spec;

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

/// PITFALL: The following function will fail to verify due to Flux implementation
/// details. Constant strings in the compiled binary will get parsed by `lower_constant`
/// in `lowering.rs`. The `Ty`pe of the constant string will be `&&str`. This is
/// due to constant promotion (https://github.com/rust-lang/const-eval/blob/master/promotion.md).
/// This is not a fundamental limitation in Flux, but is a current limitation in the
/// implementation.
pub fn identity() -> bool {
    // "cat" == "cat" //~ FAILURE to verify
    true
}

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