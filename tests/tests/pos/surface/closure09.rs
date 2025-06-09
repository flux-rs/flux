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

struct Blah(i32);

impl<P: FnOnce(i32) -> i32> Blah {
    #[flux::sig(fn(self: &Self, f: P) -> i32[100]
                where P: FnOnce(i32[@king]) -> i32[king+1])]
    fn test1(self, f: P) -> i32 {
        f(self.0)
    }
}
