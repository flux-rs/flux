#![feature(step_trait, allocator_api)]
#![allow(unused)]

extern crate flux_core;

#[path = "../../lib/vec.rs"]
mod vec;

#[flux_rs::sig(fn (bool[true]))]
pub fn assert(b: bool) {}

trait Bob {
    #[flux_rs::trusted_impl]
    fn foreach<F>(&self, f: F) -> ()
    where
        F: FnMut(usize) -> ();
}

impl Bob for Vec<i32> {
    #[flux_rs::sig(fn (self: &Vec<i32>[@n], f: F) -> ()
                   where F: FnMut(usize{v:v < n}) -> ())]
    fn foreach<F>(&self, mut f: F) -> ()
    where
        F: FnMut(usize) -> (),
    {
        (0..self.len()).for_each(|i| f(i));
    }
}

impl Bob for core::ops::Range<usize> {
    #[flux_rs::sig(fn (&Self[@s], f: F) -> ()
                       where F: FnMut(usize{v:s.start <=v && v < s.end}) -> ())]
    fn foreach<F>(&self, mut f: F) -> ()
    where
        F: FnMut(usize) -> (),
    {
        let mut i = self.start;
        while i < self.end {
            f(i);
            i += 1;
        }
    }
}

#[flux_rs::sig(fn (vec1: &Vec<i32>[@n], vec2: &Vec<i32>[n]) -> i32)]
fn dot(vec1: &Vec<i32>, vec2: &Vec<i32>) -> i32 {
    let mut res = 0;
    vec1.foreach(|i| res += vec1[i] * vec2[i]);
    res
}

#[flux_rs::sig(fn (vec1: &Vec<i32>[@n], vec2: &Vec<i32>[n]) -> i32)]
fn dot2(vec1: &Vec<i32>, vec2: &Vec<i32>) -> i32 {
    let n = vec1.len();
    let mut res = 0;
    (0..n).foreach(|i| res += vec1[i] * vec2[i]);
    res
}
