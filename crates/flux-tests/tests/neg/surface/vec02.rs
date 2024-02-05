#![feature(allocator_api)]
#![feature(associated_type_bounds)]

use std::ops::Index;

#[path = "../../lib/vec.rs"]
mod vec;

// ---------------------------------------------------------------------------------------

pub fn test_get0(xs: &Vec<i32>) -> &i32 {
    <Vec<i32> as Index<usize>>::index(xs, 10) //~ ERROR refinement type
}

pub fn test_get1(xs: &Vec<i32>) -> i32 {
    xs[10] //~ ERROR refinement type
}

#[flux::sig(fn (&Vec<i32>[100]) -> &i32)]
pub fn test_get2(xs: &Vec<i32>) -> &i32 {
    <Vec<i32> as Index<usize>>::index(xs, 99)
}

#[flux::sig(fn (&Vec<i32>[100]) -> i32)]
pub fn test_get3(xs: &Vec<i32>) -> i32 {
    xs[99]
}

pub fn test_set0(xs: &mut Vec<i32>) {
    xs[10] = 100; //~ ERROR refinement type
}

#[flux::sig(fn (&mut Vec<i32>[100]))]
pub fn test_set1(xs: &mut Vec<i32>) {
    xs[99] = 100;
}

pub fn test1() {
    let mut xs = Vec::<i32>::new();
    xs.push(10);
    xs.push(20);
    xs.push(30);

    xs[0] = 100;
    xs[1] = 100;
    xs[2] = 100;
    xs[10] = 100; //~ ERROR refinement type
}

pub fn test2(xs: Vec<i32>, i: usize) {
    if i < xs.len() {
        let _ = xs[i];
        let _ = xs[i + 1]; //~ ERROR refinement type
    }
}
