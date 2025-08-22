#[flux::sig(fn (frog: F) -> i32{v:0<=v} where F: FnOnce(i32{v:0 <= v}) -> i32{v:0 <= v})]
fn test001<F>(frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    frog(99)
}

fn test001_client() {
    test001(|x| x);
}

#[flux::sig(fn (frog: F) -> i32{v:0<=v} where F: Fn(i32{v:0 <= v}) -> i32{v:0 <= v})]
fn test002<F>(frog: F) -> i32
where
    F: Fn(i32) -> i32,
{
    frog(99)
}

fn test002_client() {
    test002(|x| x);
}
