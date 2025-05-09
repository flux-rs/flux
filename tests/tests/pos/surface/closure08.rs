
#[flux::sig(fn (f: F) -> i32[100]
            where F: FnOnce(i32[@king]) -> i32[king+1])]
pub fn test0<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(99)
}

#[flux::sig(fn (f: Frog) -> i32[100]
            where Frog: FnOnce(i32[@zong]) -> i32[zong+1])]
pub fn client1<Frog>(f: Frog) -> i32
where
    Frog: FnOnce(i32) -> i32,
{
    test0(f)
}
