#![flux::opts(check_overflow = "strict-under")]

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

static TABLE: [u8; 256] = [0; 256];

pub fn lookup(b: u8) -> u8 {
    TABLE[b as usize]
}

fn int_bounds(x: i32) {
    assert(x >= i32::MIN);
    assert(x <= i32::MAX);
}

fn uint_bounds(x: u32) {
    assert(x <= u32::MAX);
}

#[flux::sig(fn(&[T][@len]) ensures T::size_of() * len <= isize::MAX)]
fn generic<T>(_: &[T]) {}

#[flux::sig(fn(&[()][@len]) ensures len <= usize::MAX)]
fn zst(_: &[()]) {}
