#[flux::sig(fn (n:i32, frog: F) -> i32{v:n<=v} where F: FnOnce(i32{v:n <= v}) -> i32{v:n <= v})]
pub fn test001<F>(n: i32, frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    let a = n + 1;
    frog(a)
}

#[flux::sig(fn (n:i32, frog: F) -> i32{v:n<=v} where F: FnOnce(i32{v:n <= v}) -> i32{v:n <= v})]
pub fn test001_err<F>(n: i32, frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    frog(99) //~ ERROR refinement type
}

#[flux::sig(fn () -> i32{v:20<=v})]
pub fn test001_client_err() -> i32 {
    test001(20, |x| x - 1) //~ ERROR refinement type
}
