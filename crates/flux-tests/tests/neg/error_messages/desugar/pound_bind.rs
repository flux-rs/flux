#[flux::sig(fn() -> (i32[#n], i32[#n]))] //~ ERROR the name `n` is already used as a parameter
fn test00() -> (i32, i32) {
    (0, 0)
}
