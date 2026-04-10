extern crate flux_core;
use flux_rs::assert;

// --- index ---

pub fn test_index_oob(xs: &[i32]) {
    let _x = xs[0]; //~ ERROR possible out-of-bounds access
}

// --- first ---

pub fn test_first(xs: &[i32]) {
    assert(xs.first().is_some()); //~ ERROR refinement type error
}

// --- last ---

pub fn test_last(xs: &[i32]) {
    assert(xs.last().is_some()); //~ ERROR refinement type error
}

// --- get ---

pub fn test_get(xs: &[i32]) {
    assert(xs.get(0).is_some()); //~ ERROR refinement type error
}

pub fn test_get_unchecked_index(xs: &[i32], i: usize) {
    assert(xs.get(i).is_some()); //~ ERROR refinement type error
}

// --- first_mut / last_mut ---

pub fn test_first_mut(xs: &mut [i32]) {
    assert(xs.first_mut().is_some()); //~ ERROR refinement type error
}

pub fn test_last_mut(xs: &mut [i32]) {
    assert(xs.last_mut().is_some()); //~ ERROR refinement type error
}

// --- get_mut ---

pub fn test_get_mut(xs: &mut [i32], i: usize) {
    assert(xs.get_mut(i).is_some()); //~ ERROR refinement type error
}

// --- split_at_mut_checked ---

pub fn test_split_at_mut_checked(xs: &mut [i32], mid: usize) {
    assert(xs.split_at_mut_checked(mid).is_some()); //~ ERROR refinement type error
}

// --- split_first ---

pub fn test_split_first(xs: &[i32]) {
    assert(xs.split_first().is_some()); //~ ERROR refinement type error
}

// --- split_last ---

pub fn test_split_last(xs: &[i32]) {
    assert(xs.split_last().is_some()); //~ ERROR refinement type error
}

// --- split_at_checked ---

pub fn test_split_at_checked(xs: &[i32], mid: usize) {
    assert(xs.split_at_checked(mid).is_some()); //~ ERROR refinement type error
}
