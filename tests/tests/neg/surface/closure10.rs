#[flux::sig(fn (f: F) -> i32[100]
            where F: FnOnce(i32[@king]) -> i32[king+1])]
pub fn test0<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(99)
}

#[flux::sig(fn () -> i32[100])]
pub fn client0_err() -> i32 {
    #[flux::sig(fn (x: i32) -> i32[x+1])]
    fn inc(x: i32) -> i32 {
        x - 1 //~ ERROR refinement type
    }
    test0(inc)
}

#[flux::sig(fn () -> i32[100])]
pub fn client0_err2() -> i32 {
    #[flux::sig(fn (x: i32) -> i32[x-1])]
    fn inc(x: i32) -> i32 {
        x - 1
    }
    test0(inc) //~ ERROR refinement type
}
