#![feature(register_tool)]
#![register_tool(flux)]

use std::vec::Vec;

#[flux::alias(type Lb(n: int) = usize{v: n <= v})]
type Lb = usize;

#[flux::trusted]
fn make_vec() -> Vec<i32> {
    vec!(1,2,3)
}

#[flux::extern_spec]
#[flux::sig(fn(v: &Vec<i32>) -> Lb(9))]
fn extern_len(v: &Vec<i32>) -> Lb {
    Vec::len(&v)
}

#[flux::sig(fn() -> Lb(10))]
pub fn test() -> Lb {
    Vec::len(&make_vec())
} //~ ERROR postcondition
