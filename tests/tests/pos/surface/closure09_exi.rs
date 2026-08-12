#[flux::sig(fn (f: F) -> i32{v: 99 < v}
            where F: FnOnce(i32[@king]) -> i32{v : king < v})]
pub fn test0<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(99)
}

#[flux::sig(fn () -> i32{v: 99 < v})]
pub fn client0() -> i32 {
    test0(|z| z + 1)
}
