#[flux::sig(fn (frog: F) -> i32{v:0<=v} where F: FnOnce(i32{v:1000 <= v}) -> i32{v:0 <= v})]
fn test001_err<F>(frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    frog(99) //~ ERROR refinement type
}

#[flux::sig(fn (frog: F) -> i32{v:0<=v} where F: FnOnce(i32{v:0 <= v}) -> i32{v:0 <= v})]
fn test001<F>(frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    frog(99)
}


fn test001_client_err() {
    test001(|x| x - 1); //~ ERROR refinement type
}

