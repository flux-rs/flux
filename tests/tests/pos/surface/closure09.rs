#[flux::sig(fn (f: F) -> i32[100]
            where F: FnOnce(i32[@king]) -> i32[king+1])]
pub fn test0<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(99)
}

#[flux::sig(fn () -> i32[100])]
pub fn client0() -> i32 {
    test0(|z| z + 1)
}
