#[flux::sig(fn (n:i32, frog: F) -> i32{v:n<=v} where F: FnOnce(i32{v:n <= v}) -> i32{v:n <= v})]
pub fn test001<F>(n: i32, frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    let a = n + 1;
    frog(a)
}

#[flux::sig(fn () -> i32{v:10<=v})]
pub fn test001_client() -> i32 {
    test001(10, |x| x + 1)
}
