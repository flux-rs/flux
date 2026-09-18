// Negative counterparts to `pos/extern_specs/flux_core_index00.rs`.
extern crate flux_core;

use core::ops::{Index, IndexMut};

use flux_rs::attrs::*;

// --- `RangeFull` yields the *whole* slice, not some other length ---

#[spec(fn(&[i32][@n]) -> &[i32][n + 1])]
fn full_is_not_longer(xs: &[i32]) -> &[i32] {
    &xs[..] //~ ERROR refinement type error
}

#[spec(fn(&[i32][@n]) -> &[i32][n - 1] requires n > 0)]
fn full_is_not_shorter(xs: &[i32]) -> &[i32] {
    &xs[..] //~ ERROR refinement type error
}

#[spec(fn(&[i32][@n]) -> &[i32][0])]
fn full_is_not_empty(xs: &[i32]) -> &[i32] {
    &xs[..] //~ ERROR refinement type error
}

// --- `IndexMut`: the `in_bounds` precondition is real ---

#[refined_by(len: int)]
pub struct Buf<'a> {
    #[field(&mut [i32][len])]
    inner: &'a mut [i32],
}

impl<'a> Index<usize> for Buf<'a> {
    #![reft(fn in_bounds(v: Buf, idx: int) -> bool { idx < v.len })]

    type Output = i32;

    #[sig(fn(&Buf[@v], {usize[@i] | i < v.len}) -> &i32)]
    fn index(&self, i: usize) -> &i32 {
        &self.inner[i]
    }
}

impl<'a> IndexMut<usize> for Buf<'a> {
    #[sig(fn(&mut Buf[@v], {usize[@i] | i < v.len}) -> &mut i32)]
    fn index_mut(&mut self, i: usize) -> &mut i32 {
        &mut self.inner[i]
    }
}

// An arbitrary index is not known to be in bounds.
#[spec(fn(&mut Buf[@v], usize))]
fn write_unchecked(buf: &mut Buf, i: usize) {
    buf[i] = 0; //~ ERROR refinement type error
}

// `len` is not known to be positive.
#[spec(fn(&mut Buf[@v]))]
fn write_first_unchecked(buf: &mut Buf) {
    buf[0] = 0; //~ ERROR refinement type error
}

// The bound is strict: `i == len` is out of bounds.
#[spec(fn(&mut Buf[@v], usize{i: i <= v.len}))]
fn write_off_by_one(buf: &mut Buf, i: usize) {
    buf[i] = 0; //~ ERROR refinement type error
}
