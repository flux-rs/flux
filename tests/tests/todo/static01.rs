#[flux::static([u32{v: v < 1000}; _])]
static XS: [u32; 5] = [1, 2, 3, 4, 5];

#[flux::sig(fn () -> bool[true])]
pub fn test_fails() -> bool {
    let a = XS[0];
    a < 1000
}

// This works fine... but the above version with the `static` does not.
#[flux::sig(fn () -> bool[true])]
pub fn test_ok() -> bool {
    let xs = [1, 2, 3, 4, 5];
    let a = xs[0];
    a < 1000
}
