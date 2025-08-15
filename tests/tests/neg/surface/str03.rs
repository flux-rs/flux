#![allow(dead_code)]
#![flux::defs {
    fn eq_len(x:str, y:str) -> bool {
        str_len(x) == str_len(y)
    }
}]

use flux_rs::attrs::*;

#[spec(fn(&str[@x], &str[@y]) requires eq_len(x, y))]
pub fn require_equal(_x: &str, _y: &str) {}

pub fn test() {
    let cat = "cat";
    let dog = "dog";
    let mouse = "mouse";
    require_equal(cat, dog);
    require_equal(cat, mouse); //~ ERROR refinement type
}
