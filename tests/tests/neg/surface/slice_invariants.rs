//! Check that slice length bounds distinguish non-ZST and ZST elements.

#![flux::opts(check_overflow = "strict")]

#[flux::sig(fn(&[u8][@len]) ensures len * 4 <= isize::MAX)]
fn non_zst(_: &[u8]) {} //~ ERROR refinement type

#[flux::sig(fn(&[()][@len]) ensures len <= isize::MAX)]
fn zst(_: &[()]) {} //~ ERROR refinement type
