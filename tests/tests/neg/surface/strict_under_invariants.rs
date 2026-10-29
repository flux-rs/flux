#![flux::opts(check_overflow = "strict-under")]

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

#[allow(unused_comparisons)]
fn uint_bounds(x: u8) {
    assert(x <= 254); //~ ERROR refinement type
}

#[flux::sig(fn(&[u8][@len]) ensures len * 4 <= isize::MAX)]
fn non_zst(_: &[u8]) {} //~ ERROR refinement type

#[flux::sig(fn(&[()][@len]) ensures len <= isize::MAX)]
fn zst(_: &[()]) {} //~ ERROR refinement type

#[allow(unconditional_panic)]
pub fn out_of_bounds(b: u8) -> u8 {
    let table = [0; 255];
    table[b as usize] //~ ERROR assertion might fail
}
