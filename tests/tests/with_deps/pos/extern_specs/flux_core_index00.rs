// Specs for `SliceIndex<[T]> for RangeFull` and the `core::ops::IndexMut` trait.
extern crate flux_core;

use core::ops::{Index, IndexMut};

use flux_rs::{assert, attrs::*};

// --- `RangeFull` ---

// A full range is always in bounds and yields the whole slice.
#[spec(fn(&[i32][@n]) -> &[i32][n])]
fn full(xs: &[i32]) -> &[i32] {
    &xs[..]
}

#[spec(fn(&mut [i32][@n]) -> &mut [i32][n])]
fn full_mut(xs: &mut [i32]) -> &mut [i32] {
    &mut xs[..]
}

#[spec(fn(&[i32][@n]))]
fn full_preserves_len(xs: &[i32]) {
    let ys = &xs[..];
    assert(ys.len() == xs.len());
}

// `RangeFull` instantiating an impl generic over `I: SliceIndex<[T]>` — the shape this exists for.
#[spec(fn(&[i32][@n]) -> usize[n])]
fn full_through_generic_index(xs: &[i32]) -> usize {
    xs.index(..).len()
}

// --- `IndexMut` trait spec ---

// A local `IndexMut` impl carrying an `in_bounds` precondition. Without the trait-level spec,
// `index_mut`'s trait signature is the unrefined lifted one and this fails impl-vs-trait subtyping.
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

// The precondition is enforced at call sites, and a known-in-bounds index is accepted.
#[spec(fn(&mut Buf[@v], usize{i: i < v.len}))]
fn write_in_bounds(buf: &mut Buf, i: usize) {
    buf[i] = 0;
}

#[spec(fn(&mut Buf[@v]) requires v.len > 0)]
fn write_first(buf: &mut Buf) {
    buf[0] = 0;
}
