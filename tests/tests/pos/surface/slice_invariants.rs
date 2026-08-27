//! Check that slice length bounds are assumed when overflow checking is enabled.

#![flux::opts(check_overflow = "strict")]

// the full spec is T::size_of() * len <= isize::MAX, which is 1 * len in this case
#[flux::sig(fn(&[u8][@len]) ensures len <= isize::MAX)]
fn non_zst_1(_: &[u8]) {}

// the full spec is T::size_of() * len <= isize::MAX, which is 4 * len in this case
#[flux::sig(fn(&[u32][@len]) ensures 4 * len <= isize::MAX)]
fn non_zst_2(_: &[u32]) {}

#[flux::sig(fn(&[()][@len]) ensures len <= usize::MAX)]
fn zst(_: &[()]) {}
