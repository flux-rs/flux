#[flux::sig(fn() -> [i32{v : v > 0}; 20])] //~ ERROR array length mismatch
pub fn array00() -> [i32; 2] {
    [10, 11]
}

#[flux::sig(fn() -> [i32{v : v > 0}; 2])]
pub fn array01() -> [i32; 1 + 1] { //~ ERROR unsupported
    [10, 11]
}
