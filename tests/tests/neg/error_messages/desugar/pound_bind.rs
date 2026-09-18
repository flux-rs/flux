#[flux::sig(fn() -> (i32[#n], i32[#n]))] //~ ERROR identifier `n` is bound more than once
fn test00() -> (i32, i32) {
    (0, 0)
}
